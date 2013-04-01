/*
 * window.c - the PuTTY(tel) main program, which runs a PuTTY terminal
 * emulator and backend in a window.
 */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <time.h>
#include <limits.h>
#include <assert.h>

#ifndef NO_MULTIMON
#define COMPILE_MULTIMON_STUBS
#endif

#define PUTTY_DO_GLOBALS        /* actually _define_ globals */
extern "C" {
#include "putty.h"
#include "terminal.h"
#include "storage.h"
#include "win_res.h"
}
#ifndef NO_MULTIMON
#include <multimon.h>
#endif
#include <imm.h>
#include <commctrl.h>
#include <richedit.h>
#include <mmsystem.h>
#include <dwmapi.h>
/* From MSDN: In the WM_SYSCOMMAND message, the four low-order bits of
 * wParam are used by Windows, and should be masked off, so we shouldn't
 * attempt to store information in them. Hence all these identifiers have
 * the low 4 bits clear. Also, identifiers should < 0xF000. */
#define IDM_SHOWLOG   0x0010
#define IDM_NEWSESS   0x0020
#define IDM_DUPSESS   0x0030
#define IDM_RESTART   0x0040
#define IDM_RECONF    0x0050
#define IDM_CLRSB     0x0060
#define IDM_RESET     0x0070
#define IDM_HELP      0x0140
#define IDM_ABOUT     0x0150
#define IDM_SAVEDSESS 0x0160
#define IDM_COPYALL   0x0170
#define IDM_FULLSCREEN	0x0180
#define IDM_PASTE     0x0190
#define IDM_SPECIALSEP 0x0200
#define IDM_SPECIAL_MIN 0x0400
#define IDM_SPECIAL_MAX 0x0800
#define IDM_SAVED_MIN 0x1000
#define IDM_SAVED_MAX 0x5000
#define MENU_SAVED_STEP 16
/* Maximum number of sessions on saved-session submenu */
#define MENU_SAVED_MAX ((IDM_SAVED_MAX-IDM_SAVED_MIN) / MENU_SAVED_STEP)
#define WM_IGNORE_CLIP (WM_APP + 2)
#define WM_FULLSCR_ON_MAX (WM_APP + 3)
#define WM_AGENT_CALLBACK (WM_APP + 4)
#define WM_GOT_CLIPDATA (WM_APP + 6)
/* Needed for Chinese support and apparently not always defined. */
#ifndef VK_PROCESSKEY
#define VK_PROCESSKEY 0xE5
#endif
/* Mouse wheel support. */
#ifndef WM_MOUSEWHEEL
#define WM_MOUSEWHEEL 0x020A    /* not defined in earlier SDKs */
#endif
#ifndef WHEEL_DELTA
#define WHEEL_DELTA 120
#endif

/* VK_PACKET, used to send Unicode characters in WM_KEYDOWNs */
#ifndef VK_PACKET
#define VK_PACKET 0xE7
#endif

static Mouse_Button translate_button(Mouse_Button button);
static LRESULT CALLBACK WndProc(HWND, UINT, WPARAM, LPARAM);
static int TranslateKey(UINT message, WPARAM wParam, LPARAM lParam,
                        unsigned char *output);
static void conftopalette(void);
static void systopalette(void);
static void init_palette(void);
static void init_fonts(int, int);
static void another_font(int);
static void deinit_fonts(void);
static void set_input_locale(HKL);
static void update_savedsess_menu(void);
static void init_winfuncs(void);

static int is_full_screen(void);
static void make_full_screen(void);
static void clear_full_screen(void);
static void flip_full_screen(void);
static int process_clipdata(HGLOBAL clipdata, int unicode);

/* Window layout information */
static void reset_window(int);
static int extra_width, extra_height;
static int box_width, box_height, font_dualwidth, font_varpitch;
static int offset_width, offset_height;
static int was_zoomed = 0;
static int prev_rows, prev_cols;

static void flash_window(int mode);
static void sys_cursor_update(void);
static int get_fullscreen_rect(RECT * ss);

static int caret_x = -1, caret_y = -1;

static int kbd_codepage;

static void *ldisc;
static Backend *back;
static void *backhandle;

static struct unicode_data ucsdata;
static int session_closed;
static int reconfiguring = FALSE;

static const struct telnet_special *specials = NULL;
static HMENU specials_menu = NULL;
static int n_specials = 0;

static wchar_t *clipboard_contents;
static size_t clipboard_length;

#define TIMING_TIMER_ID 1234
static long timing_next_time;

/* Reconnect */
#define TIMING_RECONNECT_ID 1235

static struct {
  HMENU menu;
} popup_menus[2];
enum { SYSMENU, CTXMENU };
static HMENU savedsess_menu;

struct wm_netevent_params {
  /* Used to pass data to wm_netevent_callback */
  WPARAM wParam;
  LPARAM lParam;
};

extern "C" {
   Conf *conf;            /* exported to windlg.c */
}

static void conf_cache_data(void);
int cursor_type;
int vtmode;

static struct sesslist sesslist;      /* for saved-session menu */

struct agent_callback {
  void (*callback) (void *, void *, int);
  void *callback_ctx;
  void *data;
  int len;
};

#define FONT_NORMAL 0
#define FONT_BOLD 1
#define FONT_UNDERLINE 2
#define FONT_BOLDUND 3
#define FONT_WIDE	0x04
#define FONT_HIGH	0x08
#define FONT_NARROW	0x10

#define FONT_OEM 	0x20
#define FONT_OEMBOLD 	0x21
#define FONT_OEMUND 	0x22
#define FONT_OEMBOLDUND 0x23

#define FONT_MAXNO 	0x40
#define FONT_SHIFT	5
static HFONT fonts[FONT_MAXNO];
static int fontflag[FONT_MAXNO];
static enum {
  BOLD_NONE, BOLD_SHADOW, BOLD_FONT
} bold_font_mode;
static int bold_colours;
static enum {
  UND_LINE, UND_FONT
} und_mode;

static int descent;

#define NCFGCOLOURS 24
#define NEXTCOLOURS 240
#define NALLCOLOURS (NCFGCOLOURS + NEXTCOLOURS)
static COLORREF colours[NALLCOLOURS];
static HPALETTE pal;
static LPLOGPALETTE logpal;
static RGBTRIPLE defpal[NALLCOLOURS];

static HBITMAP caretbm;

static int dbltime, lasttime, lastact;
static Mouse_Button lastbtn;

/* this allows xterm-style mouse handling. */
static int send_raw_mouse = 0;
static int wheel_accumulator = 0;

static int busy_status = BUSY_NOT;

static char *window_name, *icon_name;

static int compose_state = 0;

static UINT wm_mousewheel = WM_MOUSEWHEEL;
#define IS_HIGH_VARSEL(wch1, wch2) \
    ((wch1) == 0xDB40 && ((wch2) >= 0xDD00 && (wch2) <= 0xDDEF))
#define IS_LOW_VARSEL(wch) \
    (((wch) >= 0x180B && (wch) <= 0x180D) || /* MONGOLIAN FREE VARIATION SELECTOR */ \
     ((wch) >= 0xFE00 && (wch) <= 0xFE0F))      /* VARIATION SELECTOR 1-16 */

extern "C" const int share_can_be_downstream = TRUE;
extern "C" const int share_can_be_upstream = TRUE;

extern "C" char *do_select(SOCKET skt, int startup);

/* conf cache */
static int alt_metabit;
static int url_underline;
static int bg_effect;
static int bg_wallpaper;
static int wp_position;
static int wp_align;
static int wp_valign;
static int wp_moving;
static int pvkey_length[256][8];
static char pvkey_codes[256][8][16];

/* Reconnect */
#define WM_NOTIFY_RECONNECT (WM_USER + 1984)
static DWORD last_reconnect = 0;

/* IME */
static int ime_mode = 0;
static wchar_t ime_w[1024];
static char ime_m[512];

/* Background */

#include <d2d1.h>
#include <d2d1helper.h>
#include <dwrite.h>
#include <wincodec.h>
#ifdef __MINGW32__
#else
#include <wincodecsdk.h>
#endif
#include <Wtsapi32.h>

static void bg_create();
static void bg_release();
static void bg_resize(int draw);
static void bg_move(int draw);
static void bg_glass();
static void bm_create();
static void bm_release();
static void wp_create();
static void wp_release();
static void wp_draw(const D2D1_RECT_F * rect);

static INT bg_active = BG_ACTIVE;
static int bm_width;
static int bm_height;

/* transparency */
static FLOAT alphas[4][2];

// d2d

static ID2D1Bitmap *d2dBM = NULL;
static ID2D1BitmapBrush *d2dBB = NULL;

static ID2D1Factory *d2dF = NULL;
static IDWriteFactory *dwF = NULL;
static ID2D1StrokeStyle *d2dSS = NULL;

static ID2D1HwndRenderTarget *d2dRT = NULL;
static ID2D1SolidColorBrush *d2dSCBfg = NULL;
static ID2D1SolidColorBrush *d2dSCBbg = NULL;
static ID2D1SolidColorBrush *d2dSCBc = NULL;

enum { FF_NORMAL, FF_WIDE, FF_ALT };
enum { FF_BOLD = 1 };

static IDWriteFontFace *dwFF[3][2] = { NULL, NULL, NULL, NULL, NULL, NULL };

static FLOAT dw_width[3][2][0x10000];

static FLOAT pixelsPerDip = 1.0f;
static int font_size = 0;
static int font_ascent = 0;
static int font_descent = 0;
static int font_underline = 0;

static LOGFONTW lfontw;

#define D2D_RGB(r,g,b) ((UINT32)(((BYTE)(b)|((WORD)((BYTE)(g))<<8))|(((DWORD)(BYTE)(r))<<16)))

static void d2d_create();
static void d2d_release();
static void d2d_init();
static void d2d_deinit();
static int d2d_begin();
static void d2d_end();
static void d2d_clear();
static void d2d_resize();

static void dw_create();
static void dw_release();
static void dw_init(int size);
static void dw_deinit();
static void dw_fontface(const WCHAR * name, int charset, int size, int weight,
                        IDWriteFontFace ** fontface);
static FLOAT dw_getwidth(UINT32 index, IDWriteFontFace * fontface);
static void dw_textout(int x, int y, UINT opt, const RECT * rc,
                       WCHAR * str, UINT len, const int *dx, int wide,
                       unsigned long long attr);

static LCID getLCID(DWORD CharSet);

struct AccentPolicy {
  DWORD AccentState;
  DWORD AccentFlags;
  DWORD GradientColor;
  DWORD AnimationId;
};

struct WINCOMPATTRDATA {
  DWORD attribute;
  PVOID pData;
  ULONG dataSize;
};

DECL_WINDOWS_FUNCTION(static, HRESULT, SetWindowCompositionAttribute , (HWND, WINCOMPATTRDATA*));

extern "C" int window_begin();
extern "C" void window_end();

// cache
static int baseline_offset;
static int baseline_offset_fw;
static int border_style;
static int cleartype_level;
static int enhanced_contrast;
static int font_quality;
static int gamma;
static int line_gap;
static int rendering_mode;
static int use_altfont;
static int use_widefont;
static int window_border;

#ifndef D2DBG
#define D2DBG WriteDebugInfo
//#define D2DBG __noop
#endif
VOID WINAPI WriteDebugInfo(const char *format, ...)
{
  va_list ap;
  va_start(ap, format);
  vprintf(format, ap);
  fflush(NULL);
  va_end(ap);
}

//

/* Dummy routine, only required in plink. */
void frontend_echoedit_update(void *frontend, int echo, int edit)
{
}

char *get_ttymode(void *frontend, const char *mode)
{
  return term_get_ttymode(term, mode);
}

static void start_backend(void)
{
  const char *error;
  char msg[1024], *title;
  char *realhost;
  int i;

  /*
   * Select protocol. This is farmed out into a table in a
   * separate file to enable an ssh-free variant.
   */
  back = backend_from_proto(conf_get_int(conf, CONF_protocol));
  if (back == NULL) {
    char *str = dupprintf("%s Internal Error", appname);
    MessageBox(NULL, "Unsupported protocol number found",
               str, MB_OK | MB_ICONEXCLAMATION);
    sfree(str);
    cleanup_exit(1);
  }

  error = back->init(NULL, &backhandle, conf,
                     conf_get_str(conf, CONF_host),
                     conf_get_int(conf, CONF_port),
                     &realhost,
                     conf_get_int(conf, CONF_tcp_nodelay),
                     conf_get_int(conf, CONF_tcp_keepalives));
  back->provide_logctx(backhandle, logctx);
  /* Reconnect */
  /*
  if (error) {
    char *str = dupprintf("%s Error", appname);
    sprintf(msg, "Unable to open connection to\n"
            "%.800s\n" "%s", conf_dest(conf), error);
    MessageBox(NULL, msg, str, MB_ICONERROR | MB_OK);
    sfree(str);
    exit(0);
  }
  */
  window_name = icon_name = NULL;
  title = conf_get_str(conf, CONF_wintitle);
  if (!*title) {
    sprintf(msg, "%s - %s", realhost, appname);
    title = msg;
  }
  sfree(realhost);
  set_title(NULL, title);
  set_icon(NULL, title);

  /*
   * Connect the terminal to the backend for resize purposes.
   */
  term_provide_resize_fn(term, back->size, backhandle);

  /*
   * Set up a line discipline.
   */
  ldisc = ldisc_create(conf, term, back, backhandle, NULL);

  /*
   * Destroy the Restart Session menu item. (This will return
   * failure if it's already absent, as it will be the very first
   * time we call this function. We ignore that, because as long
   * as the menu item ends up not being there, we don't care
   * whether it was us who removed it or not!)
   */
  for (i = 0; i < lenof(popup_menus); i++) {
    DeleteMenu(popup_menus[i].menu, IDM_RESTART, MF_BYCOMMAND);
  }

  session_closed = FALSE;

  /* Reconnect */
  if (error) {
    connection_fatal(term, "Unable to open connection to\r\n"
                     "%.800s\r\n" "%s", conf_dest(conf), error);
  }
}

static void close_session(void *ignored_context)
{
  char morestuff[100];
  int i;

  session_closed = TRUE;
  sprintf(morestuff, "%.70s (inactive)", appname);
  set_icon(NULL, morestuff);
  set_title(NULL, morestuff);

  if (ldisc) {
    ldisc_free(ldisc);
    ldisc = NULL;
  }
  if (back) {
    back->free(backhandle);
    backhandle = NULL;
    back = NULL;
    term_provide_resize_fn(term, NULL, NULL);
    update_specials_menu(NULL);
  }

  /*
   * Show the Restart Session menu item. Do a precautionary
   * delete first to ensure we never end up with more than one.
   */
  for (i = 0; i < lenof(popup_menus); i++) {
    DeleteMenu(popup_menus[i].menu, IDM_RESTART, MF_BYCOMMAND);
    InsertMenu(popup_menus[i].menu, IDM_DUPSESS, MF_BYCOMMAND | MF_ENABLED,
               IDM_RESTART, "&Restart Session");
  }
}

extern "C" int use_inifile;
extern "C" char inifile[2 * MAX_PATH + 10];
extern "C" void cleanup_all(void);

int WINAPI WinMain(HINSTANCE inst, HINSTANCE prev, LPSTR cmdline, int show)
{
  MSG msg;
  HRESULT hr;
  int guess_width, guess_height;

  hinst = inst;
  hwnd = NULL;
  flags = FLAG_VERBOSE | FLAG_INTERACTIVE;

  sk_init();

  InitCommonControls();

  /* Ensure a Maximize setting in Explorer doesn't maximise the
   * config box. */
  defuse_showwindow();

  if (!init_winver()) {
    char *str = dupprintf("%s Fatal Error", appname);
    MessageBox(NULL, "Windows refuses to report a version",
               str, MB_OK | MB_ICONEXCLAMATION);
    sfree(str);
    return 1;
  }

  /*
   * If we're running a version of Windows that doesn't support
   * WM_MOUSEWHEEL, find out what message number we should be
   * using instead.
   */
  if (osVersion.dwMajorVersion < 4 ||
      (osVersion.dwMajorVersion == 4 &&
       osVersion.dwPlatformId != VER_PLATFORM_WIN32_NT))
    wm_mousewheel = RegisterWindowMessage("MSWHEEL_ROLLMSG");

  init_help();

  init_winfuncs();

  conf = conf_new();

  /*
   * Initialize COM.
   */
  hr = CoInitialize(NULL);
  if (hr != S_OK && hr != S_FALSE) {
    char *str = dupprintf("%s Fatal Error", appname);
    MessageBox(NULL, "Failed to initialize COM subsystem",
               str, MB_OK | MB_ICONEXCLAMATION);
    sfree(str);
    return 1;
  }

  /*
   * Process the command line.
   */
  {
    char *p;
    int got_host = 0;
    /* By default, we bring up the config dialog, rather than launching
     * a session. This gets set to TRUE if something happens to change
     * that (e.g., a hostname is specified on the command-line). */
    int allow_launch = FALSE;
    int argc;
    char **argv;

    default_protocol = be_default_protocol;
    /* Find the appropriate default port. */
    {
      Backend *b = backend_from_proto(default_protocol);
      default_port = 0; /* illegal */
      if (b)
        default_port = b->default_port;
    }
    conf_set_int(conf, CONF_logtype, LGTYP_NONE);

    split_into_argv(cmdline, &argc, &argv, NULL);

    if (argc > 1 && !strcmp(argv[0], "-ini") && *(argv[1]) != '\0') {
      char *dummy;
      DWORD attributes;
      GetFullPathName(argv[1], sizeof inifile, inifile, &dummy);
      attributes = GetFileAttributes(inifile);
      if (attributes != 0xFFFFFFFF &&
          (attributes & FILE_ATTRIBUTE_DIRECTORY) == 0) {
        HANDLE handle = CreateFile(inifile, GENERIC_READ | GENERIC_WRITE,
                                   FILE_SHARE_READ | FILE_SHARE_WRITE, NULL,
                                   OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
        if (handle != INVALID_HANDLE_VALUE) {
          CloseHandle(handle);
          use_inifile = 1;
          argc -= 2;
          argv += 2;
        }
      } else {
        cmdline_error("cannot read .ini file \"%s\"", inifile);
      }
    }

    do_defaults(NULL, conf);

    p = cmdline;

    /*
     * Process a couple of command-line options which are more
     * easily dealt with before the line is broken up into words.
     * These are the old-fashioned but convenient @sessionname and
     * the internal-use-only &sharedmemoryhandle, neither of which
     * are combined with anything else.
     */
    while (*p && isspace(*p))
      p++;
    if (*p == '@') {
      /*
       * An initial @ means that the whole of the rest of the
       * command line should be treated as the name of a saved
       * session, with _no quoting or escaping_. This makes it a
       * very convenient means of automated saved-session
       * launching, via IDM_SAVEDSESS or Windows 7 jump lists.
       */
      INT_PTR i = strlen(p);
      while (i > 1 && isspace(p[i - 1]))
        i--;
      p[i] = '\0';
      do_defaults(p + 1, conf);
      if (!conf_launchable(conf) && !do_config()) {
        cleanup_exit(0);
      }
      allow_launch = TRUE;      /* allow it to be launched directly */
    } else if (*p == '&') {
      /*
       * An initial & means we've been given a command line
       * containing the hex value of a HANDLE for a file
       * mapping object, which we must then interpret as a
       * serialised Conf.
       */
      HANDLE filemap;
      void *cp;
      unsigned cpsize;
      if (sscanf(p + 1, "%p:%u", &filemap, &cpsize) == 2 &&
          (cp = MapViewOfFile(filemap, FILE_MAP_READ, 0, 0, cpsize)) != NULL) {
        conf_deserialise(conf, cp, cpsize);
        UnmapViewOfFile(cp);
        CloseHandle(filemap);
      } else if (!do_config()) {
        cleanup_exit(0);
      }
      allow_launch = TRUE;
    } else {
      /*
       * Otherwise, break up the command line and deal with
       * it sensibly.
       */
      int i;
      for (i = 0; i < argc; i++) {
        char *p = argv[i];
        int ret;

        ret = cmdline_process_param(p, i + 1 < argc ? argv[i + 1] : NULL,
                                    1, conf);
        if (ret == -2) {
          cmdline_error("option \"%s\" requires an argument", p);
        } else if (ret == 2) {
          i++;  /* skip next argument */
        } else if (ret == 1) {
          continue;     /* nothing further needs doing */
        } else if (!strcmp(p, "-cleanup") ||
                   !strcmp(p, "-cleanup-during-uninstall")) {
          /*
           * `putty -cleanup'. Remove all registry
           * entries associated with PuTTY, and also find
           * and delete the random seed file.
           */
          char *s1, *s2;
          /* Are we being invoked from an uninstaller? */
          if (!strcmp(p, "-cleanup-during-uninstall")) {
            s1 = dupprintf("Remove saved sessions and random seed file?\n"
                           "\n"
                           "If you hit Yes, ALL Registry entries associated\n"
                           "with %s will be removed, as well as the\n"
                           "random seed file. THIS PROCESS WILL\n"
                           "DESTROY YOUR SAVED SESSIONS.\n"
                           "(This only affects the currently logged-in user.)\n"
                           "\n"
                           "If you hit No, uninstallation will proceed, but\n"
                           "saved sessions etc will be left on the machine.",
                           appname);
            s2 = dupprintf("%s Uninstallation", appname);
          } else {
            s1 = dupprintf("This procedure will remove ALL Registry entries\n"
                           "associated with %s, and will also remove\n"
                           "the random seed file. (This only affects the\n"
                           "currently logged-in user.)\n"
                           "\n"
                           "THIS PROCESS WILL DESTROY YOUR SAVED SESSIONS.\n"
                           "Are you really sure you want to continue?",
                           appname);
            s2 = dupprintf("%s Warning", appname);
          }
          if (message_box(s1, s2,
                          MB_YESNO | MB_ICONWARNING | MB_DEFBUTTON2,
                          HELPCTXID(option_cleanup)) == IDYES) {
            cleanup_all();
          }
          sfree(s1);
          sfree(s2);
          exit(0);
        } else if (!strcmp(p, "-pgpfp")) {
          pgp_fingerprints();
          exit(1);
        } else if (*p != '-') {
          char *q = p;
          if (got_host) {
            /*
             * If we already have a host name, treat
             * this argument as a port number. NB we
             * have to treat this as a saved -P
             * argument, so that it will be deferred
             * until it's a good moment to run it.
             */
            int ret = cmdline_process_param("-P", p, 1, conf);
            assert(ret == 2);
          } else if (!strncmp(q, "telnet:", 7)) {
            /*
             * If the hostname starts with "telnet:",
             * set the protocol to Telnet and process
             * the string as a Telnet URL.
             */
            char c;

            q += 7;
            if (q[0] == '/' && q[1] == '/')
              q += 2;
            conf_set_int(conf, CONF_protocol, PROT_TELNET);
            p = q;
            p += host_strcspn(p, ":/");
            c = *p;
            if (*p)
              *p++ = '\0';
            if (c == ':')
              conf_set_int(conf, CONF_port, atoi(p));
            else
              conf_set_int(conf, CONF_port, -1);
            conf_set_str(conf, CONF_host, q);
            got_host = 1;
          } else {
            /*
             * Otherwise, treat this argument as a host
             * name.
             */
            while (*p && !isspace(*p))
              p++;
            if (*p)
              *p++ = '\0';
            conf_set_str(conf, CONF_host, q);
            got_host = 1;
          }
        } else {
          cmdline_error("unknown option \"%s\"", p);
        }
      }
    }

    cmdline_run_saved(conf);

    if (loaded_session || got_host)
      allow_launch = TRUE;

    if ((!allow_launch || !conf_launchable(conf)) && !do_config()) {
      cleanup_exit(0);
    }

    /*
     * Muck about with the hostname in various ways.
     */
    {
      char *hostbuf = dupstr(conf_get_str(conf, CONF_host));
      char *host = hostbuf;
      char *p, *q;

      /*
       * Trim leading whitespace.
       */
      host += strspn(host, " \t");

      /*
       * See if host is of the form user@host, and separate
       * out the username if so.
       */
      if (host[0] != '\0') {
        char *atsign = strrchr(host, '@');
        if (atsign) {
          *atsign = '\0';
          conf_set_str(conf, CONF_username, host);
          host = atsign + 1;
        }
      }

      /*
       * Trim a colon suffix off the hostname if it's there. In
       * order to protect unbracketed IPv6 address literals
       * against this treatment, we do not do this if there's
       * _more_ than one colon.
       */
      {
        char *c = host_strchr(host, ':');

        if (c) {
          char *d = host_strchr(c+1, ':');
          if (!d)
            *c = '\0';
        }
      }

      /*
       * Remove any remaining whitespace.
       */
      p = hostbuf;
      q = host;
      while (*q) {
        if (*q != ' ' && *q != '\t')
          *p++ = *q;
        q++;
      }
      *p = '\0';

      conf_set_str(conf, CONF_host, hostbuf);
      sfree(hostbuf);
    }
  }

  if (!prev) {
    char *iconfile_path = conf_get_filename(conf, CONF_iconfile)->path;
    WNDCLASSW wndclass;

    wndclass.style = 0;
    wndclass.lpfnWndProc = WndProc;
    wndclass.cbClsExtra = 0;
    wndclass.cbWndExtra = 0;
    if (conf_get_int(conf, CONF_ctrl_tab_switch))
      wndclass.cbWndExtra += 8;
    wndclass.hInstance = inst;
    wndclass.hIcon = NULL;
    if (iconfile_path != NULL && strlen(iconfile_path) != 0) {
      char *buffer = dupstr(iconfile_path);
      char *comma;
      int index = 0;
      comma = strrchr(buffer, ',');
      if (comma != NULL) {
        *comma = '\0';
        index = atoi(comma + 1);
      }
      wndclass.hIcon = ExtractIcon(inst, buffer, index);
      sfree(buffer);
    }
    if (wndclass.hIcon == NULL)
      wndclass.hIcon = LoadIcon(inst, MAKEINTRESOURCE(IDI_MAINICON));
    wndclass.hCursor = LoadCursor(NULL, IDC_IBEAM);
    wndclass.hbrBackground = NULL;
    wndclass.lpszMenuName = NULL;
    wndclass.lpszClassName = dup_mb_to_wc(DEFAULT_CODEPAGE, 0, appname);

    RegisterClassW(&wndclass);
  }

  memset(&ucsdata, 0, sizeof(ucsdata));

  conf_cache_data();

  conftopalette();

  /*
   * Guess some defaults for the window size. This all gets
   * updated later, so we don't really care too much. However, we
   * do want the font width/height guesses to correspond to a
   * large font rather than a small one...
   */

  box_width = 10;
  box_height = 20;
  extra_width = 25;
  extra_height = 28;
  guess_width = extra_width + box_width * conf_get_int(conf, CONF_width);
  guess_height = extra_height + box_height * conf_get_int(conf, CONF_height);
  {
    RECT r;
    get_fullscreen_rect(&r);
    if (guess_width > r.right - r.left)
      guess_width = r.right - r.left;
    if (guess_height > r.bottom - r.top)
      guess_height = r.bottom - r.top;
  }

  {
    int winmode = WS_OVERLAPPEDWINDOW | WS_VSCROLL;
    int exwinmode = 0;
    wchar_t *uappname = dup_mb_to_wc(DEFAULT_CODEPAGE, 0, appname);
    if (!conf_get_int(conf, CONF_scrollbar))
      winmode &= ~(WS_VSCROLL);
    if (conf_get_int(conf, CONF_resize_action) == RESIZE_DISABLED)
      winmode &= ~(WS_THICKFRAME | WS_MAXIMIZEBOX);
    if (conf_get_int(conf, CONF_alwaysontop))
      exwinmode |= WS_EX_TOPMOST;
    if (conf_get_int(conf, CONF_sunken_edge))
      exwinmode |= WS_EX_CLIENTEDGE;
    hwnd = CreateWindowExW(exwinmode, uappname, uappname,
                          winmode, conf_get_int(conf, CONF_x),
                          conf_get_int(conf, CONF_y), guess_width,
                          guess_height, NULL, NULL, inst, NULL);
    sfree(uappname);
  }

  /*
   * Initialise the terminal. (We have to do this _after_
   * creating the window, since the terminal is the first thing
   * which will call schedule_timer(), which will in turn call
   * timer_change_notify() which will expect hwnd to exist.)
   */
  term = term_init(conf, &ucsdata, NULL);
  logctx = log_init(NULL, conf);
  term_provide_logctx(term, logctx);
  term_size(term, conf_get_int(conf, CONF_height),
            conf_get_int(conf, CONF_width),
            conf_get_int(conf, CONF_savelines));

  // d2d
  d2d_create();
  dw_create();
  d2d_init();

  /*
   * Initialise the fonts, simultaneously correcting the guesses
   * for font_{width,height}.
   */
  init_fonts(0, 0);

  /*
   * Correct the guesses for extra_{width,height}.
   */
  {
    RECT cr, wr;
    GetWindowRect(hwnd, &wr);
    GetClientRect(hwnd, &cr);
    offset_width = offset_height = conf_get_int(conf, CONF_window_border);
    extra_width = wr.right - wr.left - cr.right + cr.left + offset_width * 2;
    extra_height = wr.bottom - wr.top - cr.bottom + cr.top + offset_height * 2;
  }

  /*
   * Resize the window, now we know what size we _really_ want it
   * to be.
   */
  guess_width = extra_width + box_width * term->cols;
  guess_height = extra_height + box_height * term->rows;
  SetWindowPos(hwnd, NULL, 0, 0, guess_width, guess_height,
               SWP_NOMOVE | SWP_NOREDRAW | SWP_NOZORDER);

  // d2d
  // /*
  //  * Set up a caret bitmap, with no content.
  //  */
  // {
  //   char *bits;
  //   int size = (box_width + 15) / 16 * 2 * box_height;
  //   bits = snewn(size, char);
  //   memset(bits, 0, size);
  //   caretbm = CreateBitmap(box_width, box_height, 1, 1, bits);
  //   sfree(bits);
  // }
  // CreateCaret(hwnd, caretbm, box_width, box_height);
  //

  /*
   * Initialise the scroll bar.
   */
  {
    SCROLLINFO si;

    si.cbSize = sizeof(si);
    si.fMask = SIF_ALL | SIF_DISABLENOSCROLL;
    si.nMin = 0;
    si.nMax = term->rows - 1;
    si.nPage = term->rows;
    si.nPos = 0;
    SetScrollInfo(hwnd, SB_VERT, &si, FALSE);
  }

  /*
   * Prepare the mouse handler.
   */
  lastact = MA_NOTHING;
  lastbtn = MBT_NOTHING;
  dbltime = GetDoubleClickTime();

  /*
   * Set up the session-control options on the system menu.
   */
  {
    HMENU m;
    int j;
    char *str;

    popup_menus[SYSMENU].menu = GetSystemMenu(hwnd, FALSE);
    popup_menus[CTXMENU].menu = CreatePopupMenu();
    AppendMenu(popup_menus[CTXMENU].menu, MF_ENABLED, IDM_PASTE, "&Paste");

    savedsess_menu = CreateMenu();
    get_sesslist(&sesslist, TRUE);
    update_savedsess_menu();

    for (j = 0; j < lenof(popup_menus); j++) {
      m = popup_menus[j].menu;

      AppendMenu(m, MF_SEPARATOR, 0, 0);
      AppendMenu(m, MF_ENABLED, IDM_SHOWLOG, "&Event Log");
      AppendMenu(m, MF_SEPARATOR, 0, 0);
      AppendMenu(m, MF_ENABLED, IDM_NEWSESS, "Ne&w Session...");
      AppendMenu(m, MF_ENABLED, IDM_DUPSESS, "&Duplicate Session");
      AppendMenu(m, MF_POPUP | MF_ENABLED, (UINT_PTR) savedsess_menu,
                 "Sa&ved Sessions");
      AppendMenu(m, MF_ENABLED, IDM_RECONF, "Chan&ge Settings...");
      AppendMenu(m, MF_SEPARATOR, 0, 0);
      AppendMenu(m, MF_ENABLED, IDM_COPYALL, "C&opy All to Clipboard");
      AppendMenu(m, MF_ENABLED, IDM_CLRSB, "C&lear Scrollback");
      AppendMenu(m, MF_ENABLED, IDM_RESET, "Rese&t Terminal");
      AppendMenu(m, MF_SEPARATOR, 0, 0);
      AppendMenu(m, (conf_get_int(conf, CONF_resize_action)
                     == RESIZE_DISABLED) ? MF_GRAYED : MF_ENABLED,
                 IDM_FULLSCREEN, "&Full Screen");
      AppendMenu(m, MF_SEPARATOR, 0, 0);
      if (has_help())
        AppendMenu(m, MF_ENABLED, IDM_HELP, "&Help");
      str = dupprintf("&About %s", appname);
      AppendMenu(m, MF_ENABLED, IDM_ABOUT, str);
      sfree(str);
    }
  }

  start_backend();

  /*
   * Set up the initial input locale.
   */
  set_input_locale(GetKeyboardLayout(0));

  /*
   * Finally show the window!
   */
  ShowWindow(hwnd, show);
  SetForegroundWindow(hwnd);

  /*
   * Set the palette up.
   */
  pal = NULL;
  logpal = NULL;
  init_palette();

  /* Background */
  bg_create();

  term_set_focus(term, GetForegroundWindow() == hwnd);
  UpdateWindow(hwnd);

  while (1) {
    HANDLE *handles;
    int nhandles, n;
    DWORD timeout;

    if (toplevel_callback_pending() ||
        PeekMessageW(&msg, NULL, 0, 0, PM_NOREMOVE)) {
      /*
       * If we have anything we'd like to do immediately, set
       * the timeout for MsgWaitForMultipleObjects to zero so
       * that we'll only do a quick check of our handles and
       * then get on with whatever that was.
       *
       * One such option is a pending toplevel callback. The
       * other is a non-empty Windows message queue, which you'd
       * think we could leave to MsgWaitForMultipleObjects to
       * check for us along with all the handles, but in fact we
       * can't because once PeekMessage in one iteration of this
       * loop has removed a message from the queue, the whole
       * queue is considered uninteresting by the next
       * invocation of MWFMO. So we check ourselves whether the
       * message queue is non-empty, and if so, set this timeout
       * to zero to ensure MWFMO doesn't block.
       */
      timeout = 0;
    } else {
      timeout = INFINITE;
      /* The messages seem unreliable; especially if we're being tricky */
      term_set_focus(term, GetForegroundWindow() == hwnd);
    }

    handles = handle_get_events(&nhandles);

    n = MsgWaitForMultipleObjects(nhandles, handles, FALSE,
                                  timeout, QS_ALLINPUT);

    if ((unsigned)(n - WAIT_OBJECT_0) < (unsigned)nhandles) {
      handle_got_event(handles[n - WAIT_OBJECT_0]);
      sfree(handles);
    } else
      sfree(handles);

    while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE)) {
      if (msg.message == WM_QUIT)
        goto finished;       /* two-level break */

      if (!(IsWindow(logbox) && IsDialogMessage(logbox, &msg)))
        DispatchMessageW(&msg);

        /*
         * WM_NETEVENT messages seem to jump ahead of others in
         * the message queue. I'm not sure why; the docs for
         * PeekMessage mention that messages are prioritised in
         * some way, but I'm unclear on which priorities go where.
         *
         * Anyway, in practice I observe that WM_NETEVENT seems to
         * jump to the head of the queue, which means that if we
         * were to only process one message every time round this
         * loop, we'd get nothing but NETEVENTs if the server
         * flooded us with data, and stop responding to any other
         * kind of window message. So instead, we keep on round
         * this loop until we've consumed at least one message
         * that _isn't_ a NETEVENT, or run out of messages
         * completely (whichever comes first). And we don't go to
         * run_toplevel_callbacks (which is where the netevents
         * are actually processed, causing fresh NETEVENT messages
         * to appear) until we've done this.
         */
      if (msg.message != WM_NETEVENT)
        break;
    }

    run_toplevel_callbacks();
  }

 finished:
  cleanup_exit(msg.wParam);       /* this doesn't return... */
  return msg.wParam;       /* ... but optimiser doesn't know */
}

/*
 * Clean up and exit.
 */
void cleanup_exit(int code)
{
  /*
   * Clean up.
   */
  deinit_fonts();
  sfree(logpal);
  if (pal)
    DeleteObject(pal);
  sk_cleanup();

  if (conf_get_int(conf, CONF_protocol) == PROT_SSH) {
    random_save_seed();
#ifdef MSCRYPTOAPI
    crypto_wrapup();
#endif
  }
  shutdown_help();

  /* Clean up COM. */
  CoUninitialize();

  // d2d
  bg_release();
  dw_release();
  d2d_release();

  exit(code);
}

/*
 * Set up, or shut down, an AsyncSelect. Called from winnet.c.
 */
char *do_select(SOCKET skt, int startup)
{
  int msg, events;
  if (startup) {
    msg = WM_NETEVENT;
    events = (FD_CONNECT | FD_READ | FD_WRITE | FD_OOB | FD_CLOSE | FD_ACCEPT);
  } else {
    msg = events = 0;
  }
  if (!hwnd)
    return "do_select(): internal error (hwnd==NULL)";
  if (p_WSAAsyncSelect(skt, hwnd, msg, events) == SOCKET_ERROR) {
    switch (p_WSAGetLastError()) {
    case WSAENETDOWN:
      return "Network is down";
    default:
      return "WSAAsyncSelect(): unknown error";
    }
  }
  return NULL;
}

/*
 * Refresh the saved-session submenu from `sesslist'.
 */
static void update_savedsess_menu(void)
{
  int i;
  while (DeleteMenu(savedsess_menu, 0, MF_BYPOSITION));
  /* skip sesslist.sessions[0] == Default Settings */
  for (i = 1;
       i < ((sesslist.nsessions <= MENU_SAVED_MAX + 1) ? sesslist.nsessions
            : MENU_SAVED_MAX + 1); i++)
    AppendMenu(savedsess_menu, MF_ENABLED,
               IDM_SAVED_MIN + (i - 1) * MENU_SAVED_STEP,
               sesslist.sessions[i]);
  if (sesslist.nsessions <= 1)
    AppendMenu(savedsess_menu, MF_GRAYED, IDM_SAVED_MIN, "(No sessions)");
}

/*
 * Update the Special Commands submenu.
 */
void update_specials_menu(void *frontend)
{
  HMENU new_menu;
  int i, j, k;

  if (back)
    specials = back->get_specials(backhandle);
  else
    specials = NULL;

  if (specials) {
    /* We can't use Windows to provide a stack for submenus, so
     * here's a lame "stack" that will do for now. */
    HMENU saved_menu = NULL;
    int nesting = 1;
    new_menu = CreatePopupMenu();
    for (i = 0; nesting > 0; i++) {
      assert(IDM_SPECIAL_MIN + 0x10 * i < IDM_SPECIAL_MAX);
      switch (specials[i].code) {
      case TS_SEP:
        AppendMenu(new_menu, MF_SEPARATOR, 0, 0);
        break;
      case TS_SUBMENU:
        assert(nesting < 2);
        nesting++;
        saved_menu = new_menu;  /* XXX lame stacking */
        new_menu = CreatePopupMenu();
        AppendMenu(saved_menu, MF_POPUP | MF_ENABLED,
                   (UINT_PTR) new_menu, specials[i].name);
        break;
      case TS_EXITMENU:
        nesting--;
        if (nesting) {
          new_menu = saved_menu;        /* XXX lame stacking */
          saved_menu = NULL;
        }
        break;
      default:
        AppendMenu(new_menu, MF_ENABLED, IDM_SPECIAL_MIN + 0x10 * i,
                   specials[i].name);
        break;
      }
    }
    /* Squirrel the highest special. */
    n_specials = i - 1;
  } else {
    new_menu = NULL;
    n_specials = 0;
  }

  for (j = 0; j < lenof(popup_menus); j++) {
    if (specials_menu) {
      /* XXX does this free up all submenus? */
      for (k = GetMenuItemCount(popup_menus[j].menu) - 1; k >= 0; k--) {
        if (GetMenuItemID(popup_menus[j].menu, k) == IDM_SPECIALSEP) {
          DeleteMenu(popup_menus[j].menu, k - 1, MF_BYPOSITION);
          break;
        }
      }
      DeleteMenu(popup_menus[j].menu, IDM_SPECIALSEP, MF_BYCOMMAND);
    }
    if (new_menu) {
      InsertMenu(popup_menus[j].menu, IDM_SHOWLOG,
                 MF_BYCOMMAND | MF_POPUP | MF_ENABLED,
                 (UINT_PTR) new_menu, "S&pecial Command");
      InsertMenu(popup_menus[j].menu, IDM_SHOWLOG,
                 MF_BYCOMMAND | MF_SEPARATOR, IDM_SPECIALSEP, 0);
    }
  }
  specials_menu = new_menu;
}

static void update_mouse_pointer(void)
{
  LPTSTR curstype;
  int force_visible = FALSE;
  static int forced_visible = FALSE;
  switch (busy_status) {
  case BUSY_NOT:
    if (send_raw_mouse)
      curstype = IDC_ARROW;
    else
      curstype = IDC_IBEAM;
    break;
  case BUSY_WAITING:
    curstype = IDC_APPSTARTING; /* this may be an abuse */
    force_visible = TRUE;
    break;
  case BUSY_CPU:
    curstype = IDC_WAIT;
    force_visible = TRUE;
    break;
  default:
    assert(0);
  }
  {
    HCURSOR cursor = LoadCursor(NULL, curstype);
    SetClassLongPtr(hwnd, GCLP_HCURSOR, (LONG_PTR) cursor);
    SetCursor(cursor);  /* force redraw of cursor at current posn */
  }
  if (force_visible != forced_visible) {
    /* We want some cursor shapes to be visible always.
     * Along with show_mouseptr(), this manages the ShowCursor()
     * counter such that if we switch back to a non-force_visible
     * cursor, the previous visibility state is restored. */
    ShowCursor(force_visible);
    forced_visible = force_visible;
  }
}

void set_busy_status(void *frontend, int status)
{
  busy_status = status;
  update_mouse_pointer();
}

/*
 * set or clear the "raw mouse message" mode
 */
void set_raw_mouse_mode(void *frontend, int activate)
{
  activate = activate && !conf_get_int(conf, CONF_no_mouse_rep);
  send_raw_mouse = activate;
  update_mouse_pointer();
}

/* Reconnect */
void reconnect()
{
  DWORD tnow = GetTickCount();
  KillTimer(hwnd, TIMING_RECONNECT_ID);
  if (back) {
    return;
  }
  if (last_reconnect > tnow) {
    last_reconnect = tnow;
  }
  if (last_reconnect && (tnow - last_reconnect) < 3000) {
    SetTimer(hwnd, TIMING_RECONNECT_ID, 500, NULL);
    return;
  }
  logevent(NULL, "Reconnecting...");
  term_data(term, TRUE, ". Reconnecting...", strlen(". Reconnecting..."));
  term_pwron(term, FALSE);
  start_backend();
  last_reconnect = GetTickCount();
}

/*
 * Print a message box and close the connection.
 */
void connection_fatal(void *frontend, const char *fmt, ...)
{
  va_list ap;
  char *stuff, morestuff[100];

  va_start(ap, fmt);
  stuff = dupvprintf(fmt, ap);
  va_end(ap);

  /* Reconnect */
  if (conf_get_int(conf, CONF_failure_reconnect) ||
      conf_get_int(conf, CONF_wakeup_reconnect)) {
    close_session(NULL);
    // write the error to the terminal itself
    // someone's probably going to complain about this
    term_data(term, TRUE, stuff, strlen(stuff));
    sfree(stuff);
    PostMessage(hwnd, WM_NOTIFY_RECONNECT, 0, 0);
    return;
  }

  sprintf(morestuff, "%.70s Fatal Error", appname);
  MessageBox(hwnd, stuff, morestuff, MB_ICONERROR | MB_OK);
  sfree(stuff);

  if (conf_get_int(conf, CONF_close_on_exit) == FORCE_ON)
    PostQuitMessage(1);
  else {
    queue_toplevel_callback(close_session, NULL);
  }
}

/*
 * Report an error at the command-line parsing stage.
 */
void cmdline_error(const char *fmt, ...)
{
  va_list ap;
  char *stuff, morestuff[100];

  va_start(ap, fmt);
  stuff = dupvprintf(fmt, ap);
  va_end(ap);
  sprintf(morestuff, "%.70s Command Line Error", appname);
  MessageBox(hwnd, stuff, morestuff, MB_ICONERROR | MB_OK);
  sfree(stuff);
  exit(1);
}

extern "C" int select_result(WPARAM, LPARAM);
/*
 * Actually do the job requested by a WM_NETEVENT
 */
static void wm_netevent_callback(void *vctx)
{
  struct wm_netevent_params *params = (struct wm_netevent_params *)vctx;
  select_result(params->wParam, params->lParam);
  sfree(vctx);
}

/*
 * Copy the colour palette from the configuration data into defpal.
 * This is non-trivial because the colour indices are different.
 */
static void conftopalette(void)
{
  int i;
  static const int ww[] = {
    256, 257, 258, 259, 260, 261,
    0, 8, 1, 9, 2, 10, 3, 11,
    4, 12, 5, 13, 6, 14, 7, 15,
    262, 263
  };

  for (i = 0; i < NCFGCOLOURS; i++) {
    int w = ww[i];
    defpal[w].rgbtRed = conf_get_int_int(conf, CONF_colours, i * 3 + 0);
    defpal[w].rgbtGreen = conf_get_int_int(conf, CONF_colours, i * 3 + 1);
    defpal[w].rgbtBlue = conf_get_int_int(conf, CONF_colours, i * 3 + 2);
  }
  for (i = 0; i < NEXTCOLOURS; i++) {
    if (i < 216) {
      int r = i / 36, g = (i / 6) % 6, b = i % 6;
      defpal[i + 16].rgbtRed = r ? r * 40 + 55 : 0;
      defpal[i + 16].rgbtGreen = g ? g * 40 + 55 : 0;
      defpal[i + 16].rgbtBlue = b ? b * 40 + 55 : 0;
    } else {
      int shade = i - 216;
      shade = shade * 10 + 8;
      defpal[i + 16].rgbtRed = defpal[i + 16].rgbtGreen =
        defpal[i + 16].rgbtBlue = shade;
    }
  }

  /* Override with system colours if appropriate */
  if (conf_get_int(conf, CONF_system_colour))
    systopalette();
}

/*
 * Override bit of defpal with colours from the system.
 * (NB that this takes a copy the system colours at the time this is called,
 * so subsequent colour scheme changes don't take effect. To fix that we'd
 * probably want to be using GetSysColorBrush() and the like.)
 */
static void systopalette(void)
{
  int i;
  static const struct {
    int nIndex;
    int norm;
    int bold;
  } or_[] = {
    {
    COLOR_WINDOWTEXT, 256, 257},        /* Default Foreground */
    {
    COLOR_WINDOW, 258, 259},    /* Default Background */
    {
    COLOR_HIGHLIGHTTEXT, 260, 260},     /* Cursor Text */
    {
    COLOR_HIGHLIGHT, 261, 261}, /* Cursor Colour */
    {
    COLOR_HIGHLIGHTTEXT, 262, 262},     /* Cursor Text(IME ON) */
    {
    COLOR_HIGHLIGHT, 263, 263}, /* Cursor Colour(IME ON) */
  };

  for (i = 0; i < (sizeof(or_) / sizeof(or_[0])); i++) {
    COLORREF colour = GetSysColor(or_[i].nIndex);
    defpal[or_[i].norm].rgbtRed =
      defpal[or_[i].bold].rgbtRed = GetRValue(colour);
    defpal[or_[i].norm].rgbtGreen =
      defpal[or_[i].bold].rgbtGreen = GetGValue(colour);
    defpal[or_[i].norm].rgbtBlue =
      defpal[or_[i].bold].rgbtBlue = GetBValue(colour);
  }
}

/*
 * Set up the colour palette.
 */
static void init_palette(void)
{
  int i;
  HDC hdc = GetDC(hwnd);
  if (hdc) {
    if (conf_get_int(conf, CONF_try_palette) &&
        GetDeviceCaps(hdc, RASTERCAPS) & RC_PALETTE) {
      /*
       * This is a genuine case where we must use smalloc
       * because the snew macros can't cope.
       */
      logpal = (LPLOGPALETTE) smalloc(sizeof(*logpal)
                                      - sizeof(logpal->palPalEntry)
                                      + NALLCOLOURS * sizeof(PALETTEENTRY));
      logpal->palVersion = 0x300;
      logpal->palNumEntries = NALLCOLOURS;
      for (i = 0; i < NALLCOLOURS; i++) {
        logpal->palPalEntry[i].peRed = defpal[i].rgbtRed;
        logpal->palPalEntry[i].peGreen = defpal[i].rgbtGreen;
        logpal->palPalEntry[i].peBlue = defpal[i].rgbtBlue;
        logpal->palPalEntry[i].peFlags = PC_NOCOLLAPSE;
      }
      pal = CreatePalette(logpal);
      if (pal) {
        SelectPalette(hdc, pal, FALSE);
        RealizePalette(hdc);
        SelectPalette(hdc, (HPALETTE) GetStockObject(DEFAULT_PALETTE), FALSE);
      }
    }
    ReleaseDC(hwnd, hdc);
  }
  if (pal)
    for (i = 0; i < NALLCOLOURS; i++)
      colours[i] = PALETTERGB(defpal[i].rgbtRed,
                              defpal[i].rgbtGreen, defpal[i].rgbtBlue);
  else
    for (i = 0; i < NALLCOLOURS; i++)
      colours[i] = D2D_RGB(defpal[i].rgbtRed,
                           defpal[i].rgbtGreen, defpal[i].rgbtBlue);
}

/*
 * This is a wrapper to ExtTextOut() to force Windows to display
 * the precise glyphs we give it. Otherwise it would do its own
 * bidi and Arabic shaping, and we would end up uncertain which
 * characters it had put where.
 */
static void exact_textout(HDC hdc, int x, int y, CONST RECT * lprc,
                          unsigned short *lpString, UINT cbCount,
                          CONST INT * lpDx, int opaque)
{
  //d2d
  D2DBG("exact_textout: x=%d y=%d\n", x, y);

#ifdef __LCC__
  /*
   * The LCC include files apparently don't supply the
   * GCP_RESULTSW type, but we can make do with GCP_RESULTS
   * proper: the differences aren't important to us (the only
   * variable-width string parameter is one we don't use anyway).
   */
  GCP_RESULTS gcpr;
#else
  GCP_RESULTSW gcpr;
#endif
  char *buffer = snewn(cbCount * 2 + 2, char);
  char *classbuffer = snewn(cbCount, char);
  memset(&gcpr, 0, sizeof(gcpr));
  memset(buffer, 0, cbCount * 2 + 2);
  memset(classbuffer, GCPCLASS_NEUTRAL, cbCount);

  gcpr.lStructSize = sizeof(gcpr);
  gcpr.lpGlyphs = (LPWSTR) buffer;
  gcpr.lpClass = (LPSTR) classbuffer;
  gcpr.nGlyphs = cbCount;
  GetCharacterPlacementW(hdc, (LPCWSTR) lpString, cbCount, 0, &gcpr,
                         FLI_MASK | GCP_CLASSIN | GCP_DIACRITIC);
  ExtTextOut(hdc, x, y,
             ETO_GLYPH_INDEX | ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
             lprc, buffer, cbCount, lpDx);
}

/*
 * The exact_textout() wrapper, unfortunately, destroys the useful
 * Windows `font linking' behaviour: automatic handling of Unicode
 * code points not supported in this font by falling back to a font
 * which does contain them. Therefore, we adopt a multi-layered
 * approach: for any potentially-bidi text, we use exact_textout(),
 * and for everything else we use a simple ExtTextOut as we did
 * before exact_textout() was introduced.
 */
static void general_textout(HDC hdc, int x, int y, CONST RECT * lprc,
                            unsigned short *lpString, UINT cbCount,
                            CONST INT * lpDx, int opaque)
{
  int i, j, xp, xn;
  int bkmode = 0, got_bkmode = FALSE;

  xp = xn = x;

  for (i = 0; i < (int) cbCount;) {
    int rtl = is_rtl(lpString[i]);

    xn += lpDx[i];

    for (j = i + 1; j < (int) cbCount; j++) {
      if (rtl != is_rtl(lpString[j]))
        break;
      xn += lpDx[j];
    }

    /*
     * Now [i,j) indicates a maximal substring of lpString
     * which should be displayed using the same textout
     * function.
     */
    if (rtl) {
      exact_textout(hdc, xp, y, lprc, lpString + i, j - i,
                    font_varpitch ? NULL : lpDx + i, opaque);
    } else {
      ExtTextOutW(hdc, xp, y, ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
                  lprc, (LPCWSTR) lpString + i, j - i,
                  font_varpitch ? NULL : lpDx + i);
    }

    i = j;
    xp = xn;

    bkmode = GetBkMode(hdc);
    got_bkmode = TRUE;
    SetBkMode(hdc, TRANSPARENT);
    opaque = FALSE;
  }

  if (got_bkmode)
    SetBkMode(hdc, bkmode);
}

static void general_textout2(HDC hdc, int x, int y, CONST RECT * lprc,
                             unsigned short *lpString, UINT cbCount,
                             CONST INT * lpDx, int opaque, int wide,
                             int iso2022, unsigned long long attr)
{
  //d2d
  // D2DBG("general_textout2: x=%d y=%d lpDx=%d\n", x, y, *lpDx);

  int i, j, xp, xn;
  // int bkmode = 0, got_bkmode = FALSE;

  xp = xn = x;

  for (i = 0; i < (int) cbCount;) {
    int rtl = is_rtl(lpString[i]);

    xn += lpDx[i];

    for (j = i + 1; j < (int) cbCount; j++) {
      if (rtl != is_rtl(lpString[j]))
        break;
      xn += lpDx[j];
    }

    /*
     * Now [i,j) indicates a maximal substring of lpString
     * which should be displayed using the same textout
     * function.
     */
    if (rtl) {
      //d2d
      dw_textout(xp, y, ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
                 lprc, (WCHAR *) lpString + i, j - i, lpDx + i, wide, attr);
    } else {
      //d2d
      dw_textout(xp, y, ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
                 lprc, (WCHAR *) lpString + i, j - i, lpDx + i, wide, attr);
    }

    i = j;
    xp = xn;

    // bkmode = GetBkMode(hdc);
    // got_bkmode = TRUE;
    // SetBkMode(hdc, TRANSPARENT);
    // opaque = FALSE;
  }

  // if (got_bkmode)
  //   SetBkMode(hdc, bkmode);
}

static int get_font_width(HDC hdc, const TEXTMETRIC * tm)
{
  int ret;
  /* Note that the TMPF_FIXED_PITCH bit is defined upside down :-( */
  if (!(tm->tmPitchAndFamily & TMPF_FIXED_PITCH)) {
    ret = tm->tmAveCharWidth;
  } else {
#define FIRST '0'
#define LAST '9'
    ABCFLOAT widths[LAST - FIRST + 1];
    int j;

    font_varpitch = TRUE;
    font_dualwidth = TRUE;
    if (GetCharABCWidthsFloat(hdc, FIRST, LAST, widths)) {
      ret = 0;
      for (j = 0; j < lenof(widths); j++) {
        int width = (int) (0.5 + widths[j].abcfA +
                           widths[j].abcfB + widths[j].abcfC);
        if (ret < width)
          ret = width;
      }
    } else {
      ret = tm->tmMaxCharWidth;
    }
#undef FIRST
#undef LAST
  }
  return ret;
}

/*
 * Initialise all the fonts we will need initially. There may be as many as
 * three or as few as one.  The other (potentially) twenty-one fonts are done
 * if/when they are needed.
 *
 * We also:
 *
 * - check the font width and height, correcting our guesses if
 *   necessary.
 *
 * - verify that the bold font is the same width as the ordinary
 *   one, and engage shadow bolding if not.
 * 
 * - verify that the underlined font is the same width as the
 *   ordinary one (manual underlining by means of line drawing can
 *   be done in a pinch).
 */
static void init_fonts(int pick_width, int pick_height)
{
  //d2d
  D2DBG("init_font: %d, %d\n", pick_width, pick_height);

  TEXTMETRIC tm;
  CPINFO cpinfo;
  FontSpec *font;
  // int fontsize[3];
  int i;
  int quality;
  HDC hdc;
  int fw_dontcare, fw_bold;

  for (i = 0; i < FONT_MAXNO; i++)
    fonts[i] = NULL;

  bold_font_mode = conf_get_int(conf, CONF_bold_style) & 1 ?
    BOLD_FONT : BOLD_NONE;
  bold_colours = conf_get_int(conf, CONF_bold_style) & 2 ? TRUE : FALSE;
  und_mode = UND_FONT;

  font = conf_get_fontspec(conf, CONF_font);
  if (font->isbold) {
    fw_dontcare = FW_BOLD;
    fw_bold = FW_HEAVY;
  } else {
    fw_dontcare = FW_DONTCARE;
    fw_bold = FW_BOLD;
  }

  hdc = GetDC(hwnd);
  pixelsPerDip = (FLOAT) GetDeviceCaps(hdc, LOGPIXELSY) / 96.0f;

  if (pick_height)
    box_height = pick_height;
  else {
    box_height = font->height;
    if (box_height > 0) {
      box_height = -MulDiv(box_height, GetDeviceCaps(hdc, LOGPIXELSY), 72);
    }
  }
  box_width = pick_width;

  quality = conf_get_int(conf, CONF_font_quality);
  //d2d
  fonts[FONT_NORMAL] = CreateFontA(box_height, box_width,
                                   0, 0, fw_dontcare,
                                   FALSE, FALSE, FALSE,
                                   font->charset,
                                   OUT_DEFAULT_PRECIS,
                                   CLIP_DEFAULT_PRECIS,
                                   FONT_QUALITY(quality),
                                   FIXED_PITCH | FF_DONTCARE,
                                   font->name);

  FontSpec *widefont = conf_get_fontspec(conf, CONF_widefont);

  if (widefont->name[0]) {
    fonts[FONT_WIDE] = CreateFontA(box_height, box_width,
                                   0, 0, fw_dontcare,
                                   FALSE, FALSE, FALSE,
                                   widefont->charset,
                                   OUT_DEFAULT_PRECIS,
                                   CLIP_DEFAULT_PRECIS,
                                   FONT_QUALITY(quality),
                                   FIXED_PITCH | FF_DONTCARE,
                                   widefont->name);
  }
  // if (fonts[FONT_WIDE]) {
  //   SelectObject(hdc, fonts[FONT_WIDE]);
  //   GetObjectW(fonts[FONT_WIDE], sizeof(LOGFONTW), &lfontw);
  // } else {
  //   SelectObject(hdc, fonts[FONT_NORMAL]);
  //   GetObjectW(fonts[FONT_NORMAL], sizeof(LOGFONTW), &lfontw);
  // }

  SelectObject(hdc, fonts[FONT_NORMAL]);

  GetObjectW(fonts[FONT_NORMAL], sizeof(LOGFONTW), &lfontw);

  //d2d
  font_size = (box_height < 0) ? -box_height : box_height;
  //

  GetTextMetrics(hdc, &tm);
 
  /* Note that the TMPF_FIXED_PITCH bit is defined upside down :-( */
  if (!(tm.tmPitchAndFamily & TMPF_FIXED_PITCH)) {
    font_varpitch = FALSE;
    font_dualwidth = (tm.tmAveCharWidth != tm.tmMaxCharWidth);
  } else {
    font_varpitch = TRUE;
    font_dualwidth = TRUE;
  }
  if (pick_width == 0 || pick_height == 0) {
    box_height = tm.tmHeight;
    box_width = get_font_width(hdc, &tm);
  }
  font_dualwidth = (tm.tmAveCharWidth != tm.tmMaxCharWidth);

  D2DBG("  init_font: H=%d AvgW=%d MaxW=%d Ascent=%d Descent=%d\n",
        tm.tmHeight, tm.tmAveCharWidth, tm.tmMaxCharWidth,
        tm.tmAscent, tm.tmDescent);
  D2DBG("  init_font: font_size=%d, box_height=%d box_width=%d\n",
        font_size, box_height, box_width);

  //d2d
  dw_init(font_size);

  DWRITE_FONT_METRICS fm;
  dwFF[FF_NORMAL][FF_NORMAL]->GetGdiCompatibleMetrics((FLOAT) font_size,
                                                      pixelsPerDip, NULL, &fm);
  font_ascent =
    INT((FLOAT(fm.ascent * font_size) / fm.designUnitsPerEm) + 0.5f);
  font_descent =
    INT((FLOAT(fm.descent * font_size) / fm.designUnitsPerEm) + 0.5f);
  font_underline =
    -INT((FLOAT(-fm.underlinePosition * font_size) / fm.designUnitsPerEm) +
         0.5f);
  D2DBG("  init_font: Ascent=%d Descent=%d underlinePosition=%d\n",
        font_ascent, font_descent, font_underline);
  box_height = font_ascent + font_descent + line_gap;
  //

#ifdef RDB_DEBUG_PATCH
  debug(23, "Primary font H=%d, AW=%d, MW=%d",
        tm.tmHeight, tm.tmAveCharWidth, tm.tmMaxCharWidth);
#endif

  {
    CHARSETINFO info;
    DWORD cset = tm.tmCharSet;
    memset(&info, 0xFF, sizeof(info));

    /* !!! Yes the next line is right */
    if (cset == OEM_CHARSET)
      ucsdata.font_codepage = GetOEMCP();
    else if (TranslateCharsetInfo((DWORD *) cset, &info, TCI_SRCCHARSET))
      ucsdata.font_codepage = info.ciACP;
    else
      ucsdata.font_codepage = -1;

    GetCPInfo(ucsdata.font_codepage, &cpinfo);
    ucsdata.dbcs_screenfont = (cpinfo.MaxCharSize > 1);
  }

  //  f(FONT_UNDERLINE, font->charset, fw_dontcare, TRUE);

  /*
   * Some fonts, e.g. 9-pt Courier, draw their underlines
   * outside their character cell. We successfully prevent
   * screen corruption by clipping the text output, but then
   * we lose the underline completely. Here we try to work
   * out whether this is such a font, and if it is, we set a
   * flag that causes underlines to be drawn by hand.
   *
   * Having tried other more sophisticated approaches (such
   * as examining the TEXTMETRIC structure or requesting the
   * height of a string), I think we'll do this the brute
   * force way: we create a small bitmap, draw an underlined
   * space on it, and test to see whether any pixels are
   * foreground-coloured. (Since we expect the underline to
   * go all the way across the character cell, we only search
   * down a single column of the bitmap, half way across.)
   */
  //d2d
  // {
  //   HDC und_dc;
  //   HBITMAP und_bm, und_oldbm;
  //   int i, gotit;
  //   COLORREF c;

  //   und_dc = CreateCompatibleDC(hdc);
  //   und_bm = CreateCompatibleBitmap(hdc, box_width, box_height);
  //   und_oldbm = SelectObject(und_dc, und_bm);
  //   SelectObject(und_dc, fonts[FONT_UNDERLINE]);
  //   SetTextAlign(und_dc, TA_TOP | TA_LEFT | TA_NOUPDATECP);
  //   SetTextColor(und_dc, RGB(255, 255, 255));
  //   SetBkColor(und_dc, RGB(0, 0, 0));
  //   SetBkMode(und_dc, OPAQUE);
  //   ExtTextOut(und_dc, 0, 0, ETO_OPAQUE, NULL, " ", 1, NULL);
  //   gotit = FALSE;
  //   for (i = 0; i < box_height; i++) {
  //     c = GetPixel(und_dc, box_width / 2, i);
  //     if (c != RGB(0, 0, 0))
  //       gotit = TRUE;
  //   }
  //   SelectObject(und_dc, und_oldbm);
  //   DeleteObject(und_bm);
  //   DeleteDC(und_dc);
  //   if (!gotit) {
  //     und_mode = UND_LINE;
  //     DeleteObject(fonts[FONT_UNDERLINE]);
  //     fonts[FONT_UNDERLINE] = 0;
  //   }
  // }
  //
  // if (bold_font_mode == BOLD_FONT) {
  //   f(FONT_BOLD, font->charset, fw_bold, FALSE);
  // }
  #undef f

  descent = tm.tmAscent + 1;
  if (descent >= box_height)
    descent = box_height - 1;

  //d2d
  D2DBG(" descent: %d\n", descent);

  //d2d
  // for (i = 0; i < 3; i++) {
  //   if (fonts[i]) {
  //     if (SelectObject(hdc, fonts[i]) && GetTextMetrics(hdc, &tm))
  //       fontsize[i] = get_font_width(hdc, &tm) + 256 * tm.tmHeight;
  //     else
  //       fontsize[i] = -i;
  //   } else
  //     fontsize[i] = -i;
  // }

  ReleaseDC(hwnd, hdc);

  //d2d
  // if (fontsize[FONT_UNDERLINE] != fontsize[FONT_NORMAL]) {
  //   und_mode = UND_LINE;
  //   DeleteObject(fonts[FONT_UNDERLINE]);
  //   fonts[FONT_UNDERLINE] = 0;
  // }
  //
  // if (bold_font_mode == BOLD_FONT &&
  //     fontsize[FONT_BOLD] != fontsize[FONT_NORMAL]) {
  //   bold_font_mode = BOLD_SHADOW;
  //   DeleteObject(fonts[FONT_BOLD]);
  //   fonts[FONT_BOLD] = 0;
  // }
  fontflag[0] = fontflag[1] = fontflag[2] = 1;

  init_ucs(conf, &ucsdata);
}

static void another_font(int fontno)
{
  D2DBG("another_font: fontno=%d\n", fontno);

  int basefont;
  int fw_dontcare, fw_bold, quality;
  int c, u, w, x;
  char *s;
  FontSpec *font;

  // if (fontno < 0 || fontno >= FONT_MAXNO || fontflag[fontno])
  if (fontno < 4 || fontno >= FONT_MAXNO || fontflag[fontno])
    return;

  basefont = (fontno & ~(FONT_BOLDUND));
  if (basefont != fontno && !fontflag[basefont])
    another_font(basefont);

  font = conf_get_fontspec(conf, CONF_font);

  if (font->isbold) {
    fw_dontcare = FW_BOLD;
    fw_bold = FW_HEAVY;
  } else {
    fw_dontcare = FW_DONTCARE;
    fw_bold = FW_BOLD;
  }

  c = font->charset;
  w = fw_dontcare;
  u = FALSE;
  s = font->name;
  x = box_width;

  if (fontno & FONT_WIDE)
    x *= 2;
  if (fontno & FONT_NARROW)
    x = (x + 1) / 2;
  if (fontno & FONT_OEM)
    c = OEM_CHARSET;
  if (fontno & FONT_BOLD)
    w = fw_bold;
  if (fontno & FONT_UNDERLINE)
    u = TRUE;

  quality = conf_get_int(conf, CONF_font_quality);

  fonts[fontno] =
    CreateFont(box_height * (1 + !!(fontno & FONT_HIGH)), x, 0, 0, w,
               FALSE, u, FALSE, c, OUT_DEFAULT_PRECIS,
               CLIP_DEFAULT_PRECIS, FONT_QUALITY(quality),
               DEFAULT_PITCH | FF_DONTCARE, s);

  fontflag[fontno] = 1;
}

static void deinit_fonts(void)
{
  int i;
  for (i = 0; i < FONT_MAXNO; i++) {
    if (fonts[i])
      DeleteObject(fonts[i]);
    fonts[i] = 0;
    fontflag[i] = 0;
  }
  //d2d
  dw_deinit();
}

void request_resize(void *frontend, int w, int h)
{
  int width, height;

  /* If the window is maximized supress resizing attempts */
  if (IsZoomed(hwnd)) {
    if (conf_get_int(conf, CONF_resize_action) == RESIZE_TERM)
      return;
  }

  if (conf_get_int(conf, CONF_resize_action) == RESIZE_DISABLED)
    return;
  if (h == term->rows && w == term->cols)
    return;

  /* Sanity checks ... */
  {
    static int first_time = 1;
    static RECT ss;

    switch (first_time) {
    case 1:
      /* Get the size of the screen */
      if (get_fullscreen_rect(&ss))
        /* first_time = 0 */ ;
      else {
        first_time = 2;
        break;
      }
    case 0:
      /* Make sure the values are sane */
      width = (ss.right - ss.left - extra_width) / 4;
      height = (ss.bottom - ss.top - extra_height) / 6;

      if (w > width || h > height)
        return;
      if (w < 15)
        w = 15;
      if (h < 1)
        h = 1;
    }
  }

  term_size(term, h, w, conf_get_int(conf, CONF_savelines));

  if (conf_get_int(conf, CONF_resize_action) != RESIZE_FONT && !IsZoomed(hwnd)) {
    width = extra_width + box_width * w;
    height = extra_height + box_height * h;

    SetWindowPos(hwnd, NULL, 0, 0, width, height,
                 SWP_NOACTIVATE | SWP_NOCOPYBITS | SWP_NOMOVE | SWP_NOZORDER);
  } else
    reset_window(0);

  InvalidateRect(hwnd, NULL, TRUE);
}

static void reset_window(int reinit)
{
  /*
   * This function decides how to resize or redraw when the 
   * user changes something. 
   *
   * This function doesn't like to change the terminal size but if the
   * font size is locked that may be it's only soluion.
   */
  int win_width, win_height, resize_action, window_border;
  RECT cr, wr;

#ifdef RDB_DEBUG_PATCH
  debug((27, "reset_window()"));
#endif

  /* Current window sizes ... */
  GetWindowRect(hwnd, &wr);
  GetClientRect(hwnd, &cr);

  win_width = cr.right - cr.left;
  win_height = cr.bottom - cr.top;

  resize_action = conf_get_int(conf, CONF_resize_action);
  window_border = conf_get_int(conf, CONF_window_border);

  if (resize_action == RESIZE_DISABLED)
    reinit = 2;

  /* Are we being forced to reload the fonts ? */
  if (reinit > 1) {
#ifdef RDB_DEBUG_PATCH
    debug((27, "reset_window() -- Forced deinit"));
#endif
    deinit_fonts();
    init_fonts(0, 0);
  }

  /* Oh, looks like we're minimised */
  if (win_width == 0 || win_height == 0)
    return;

  /* Is the window out of position ? */
  if (!reinit &&
      (offset_width != (win_width - box_width * term->cols) / 2 ||
       offset_height != (win_height - box_height * term->rows) / 2)) {
    offset_width = (win_width - box_width * term->cols) / 2;
    offset_height = (win_height - box_height * term->rows) / 2;
    InvalidateRect(hwnd, NULL, TRUE);
#ifdef RDB_DEBUG_PATCH
    debug((27, "reset_window() -> Reposition terminal"));
#endif
  }

  if (IsZoomed(hwnd)) {
    /* We're fullscreen, this means we must not change the size of
     * the window so it's the font size or the terminal itself.
     */

    extra_width = wr.right - wr.left - cr.right + cr.left;
    extra_height = wr.bottom - wr.top - cr.bottom + cr.top;

    if (resize_action != RESIZE_TERM) {
      if (box_width != win_width / term->cols ||
          box_height != win_height / term->rows) {
        deinit_fonts();
        init_fonts(win_width / term->cols, win_height / term->rows);
        offset_width = (win_width - box_width * term->cols) / 2;
        offset_height = (win_height - box_height * term->rows) / 2;
        InvalidateRect(hwnd, NULL, TRUE);
#ifdef RDB_DEBUG_PATCH
        debug((25, "reset_window() -> Z font resize to (%d, %d)",
               box_width, box_height));
#endif
      }
    } else {
      if (box_width * term->cols != win_width ||
          box_height * term->rows != win_height) {
        /* Our only choice at this point is to change the 
         * size of the terminal; Oh well.
         */
        term_size(term, win_height / box_height, win_width / box_width,
                  conf_get_int(conf, CONF_savelines));
        offset_width = (win_width - box_width * term->cols) / 2;
        offset_height = (win_height - box_height * term->rows) / 2;
        InvalidateRect(hwnd, NULL, TRUE);
#ifdef RDB_DEBUG_PATCH
        debug((27, "reset_window() -> Zoomed term_size"));
#endif
      }
    }
    return;
  }

  /* Hmm, a force re-init means we should ignore the current window
   * so we resize to the default font size.
   */
  if (reinit > 0) {
#ifdef RDB_DEBUG_PATCH
    debug((27, "reset_window() -> Forced re-init"));
#endif

    offset_width = offset_height = window_border;
    extra_width = wr.right - wr.left - cr.right + cr.left + offset_width * 2;
    extra_height = wr.bottom - wr.top - cr.bottom + cr.top + offset_height * 2;

    if (win_width != box_width * term->cols + offset_width * 2 ||
        win_height != box_height * term->rows + offset_height * 2) {

      /* If this is too large windows will resize it to the maximum
       * allowed window size, we will then be back in here and resize
       * the font or terminal to fit.
       */
      SetWindowPos(hwnd, NULL, 0, 0,
                   box_width * term->cols + extra_width,
                   box_height * term->rows + extra_height,
                   SWP_NOMOVE | SWP_NOZORDER);
    }

    InvalidateRect(hwnd, NULL, TRUE);
    return;
  }

  /* Okay the user doesn't want us to change the font so we try the 
   * window. But that may be too big for the screen which forces us
   * to change the terminal.
   */
  if ((resize_action == RESIZE_TERM && reinit <= 0) ||
      (resize_action == RESIZE_EITHER && reinit < 0) || reinit > 0) {
    offset_width = offset_height = window_border;
    extra_width = wr.right - wr.left - cr.right + cr.left + offset_width * 2;
    extra_height = wr.bottom - wr.top - cr.bottom + cr.top + offset_height * 2;

    if (win_width != box_width * term->cols + offset_width * 2 ||
        win_height != box_height * term->rows + offset_height * 2) {

      static RECT ss;
      int width, height;

      get_fullscreen_rect(&ss);

      width = (ss.right - ss.left - extra_width) / box_width;
      height = (ss.bottom - ss.top - extra_height) / box_height;

      /* Grrr too big */
      if (term->rows > height || term->cols > width) {
        if (resize_action == RESIZE_EITHER) {
          /* Make the font the biggest we can */
          if (term->cols > width)
            box_width = (ss.right - ss.left - extra_width)
              / term->cols;
          if (term->rows > height)
            box_height = (ss.bottom - ss.top - extra_height)
              / term->rows;

          deinit_fonts();
          init_fonts(box_width, box_height);

          width = (ss.right - ss.left - extra_width) / box_width;
          height = (ss.bottom - ss.top - extra_height) / box_height;
        } else {
          if (height > term->rows)
            height = term->rows;
          if (width > term->cols)
            width = term->cols;
          term_size(term, height, width, conf_get_int(conf, CONF_savelines));
#ifdef RDB_DEBUG_PATCH
          debug((27, "reset_window() -> term resize to (%d,%d)",
                 height, width));
#endif
        }
      }

      SetWindowPos(hwnd, NULL, 0, 0,
                   box_width * term->cols + extra_width,
                   box_height * term->rows + extra_height,
                   SWP_NOMOVE | SWP_NOZORDER);

      InvalidateRect(hwnd, NULL, TRUE);
#ifdef RDB_DEBUG_PATCH
      debug((27, "reset_window() -> window resize to (%d,%d)",
             box_width * term->cols + extra_width,
             box_height * term->rows + extra_height));
#endif
    }
    return;
  }

  /* We're allowed to or must change the font but do we want to ?  */

  if (box_width != (win_width - window_border * 2) / term->cols ||
      box_height != (win_height - window_border * 2) / term->rows) {

    deinit_fonts();
    init_fonts((win_width - window_border * 2) / term->cols,
               (win_height - window_border * 2) / term->rows);
    offset_width = (win_width - box_width * term->cols) / 2;
    offset_height = (win_height - box_height * term->rows) / 2;

    extra_width = wr.right - wr.left - cr.right + cr.left + offset_width * 2;
    extra_height = wr.bottom - wr.top - cr.bottom + cr.top + offset_height * 2;
    //d2d
    // /* Background */
    // bg_resize(1);

    InvalidateRect(hwnd, NULL, TRUE);
#ifdef RDB_DEBUG_PATCH
    debug((25, "reset_window() -> font resize to (%d,%d)",
           box_width, box_height));
#endif
  }
}

static void set_input_locale(HKL kl)
{
  char lbuf[20];

  GetLocaleInfo(LOWORD(kl), LOCALE_IDEFAULTANSICODEPAGE, lbuf, sizeof(lbuf));

  kbd_codepage = atoi(lbuf);
}

static void click(Mouse_Button b, int x, int y, int shift, int ctrl, int alt)
{
  int thistime = GetMessageTime();

  if (send_raw_mouse && !(shift && conf_get_int(conf, CONF_mouse_override))) {
    lastbtn = MBT_NOTHING;
    term_mouse(term, b, translate_button(b), MA_CLICK, x, y, shift, ctrl, alt);
    return;
  }

  if (lastbtn == b && thistime - lasttime < dbltime) {
    lastact = (lastact == MA_CLICK ? MA_2CLK :
               lastact == MA_2CLK ? MA_3CLK :
               lastact == MA_3CLK ? MA_CLICK : MA_NOTHING);
  } else {
    lastbtn = b;
    lastact = MA_CLICK;
  }
  if (lastact != MA_NOTHING)
    term_mouse(term, b, translate_button(b),
               (Mouse_Action) lastact, x, y, shift, ctrl, alt);
  lasttime = thistime;
}

/*
 * Translate a raw mouse button designation (LEFT, MIDDLE, RIGHT)
 * into a cooked one (SELECT, EXTEND, PASTE).
 */
static Mouse_Button translate_button(Mouse_Button button)
{
  if (button == MBT_LEFT)
    return MBT_SELECT;
  if (button == MBT_MIDDLE)
    return conf_get_int(conf, CONF_mouse_is_xterm) == 1 ?
      MBT_PASTE : MBT_EXTEND;
  if (button == MBT_RIGHT)
    return conf_get_int(conf, CONF_mouse_is_xterm) == 1 ?
      MBT_EXTEND : MBT_PASTE;
  return (Mouse_Button) 0;      /* shouldn't happen */
}

static void show_mouseptr(int show)
{
  /* NB that the counter in ShowCursor() is also frobbed by
   * update_mouse_pointer() */
  static int cursor_visible = 1;
  if (!conf_get_int(conf, CONF_hide_mouseptr))
    show = 1;   /* override if this feature disabled */
  if (cursor_visible && !show)
    ShowCursor(FALSE);
  else if (!cursor_visible && show)
    ShowCursor(TRUE);
  cursor_visible = show;
}

static int is_alt_pressed(void)
{
  BYTE keystate[256];
  int r = GetKeyboardState(keystate);
  if (!r)
    return FALSE;
  if (keystate[VK_MENU] & 0x80)
    return TRUE;
  if (keystate[VK_RMENU] & 0x80)
    return TRUE;
  return FALSE;
}

struct ctrl_tab_info {
  int direction;
  HWND self;
  DWORD self_hi_date_time;
  DWORD self_lo_date_time;
  HWND next;
  DWORD next_hi_date_time;
  DWORD next_lo_date_time;
  int next_self;
};

static BOOL CALLBACK CtrlTabWindowProc(HWND hwnd, LPARAM lParam)
{
  struct ctrl_tab_info *info = (struct ctrl_tab_info *) lParam;
  char class_name[16];
  int wndExtra;
  if (info->self != hwnd
      && (wndExtra = GetClassLong(hwnd, GCL_CBWNDEXTRA)) >= 8
      && GetClassName(hwnd, class_name, sizeof class_name) >= 5
      && memcmp(class_name, "PuTTY", 5) == 0) {
    DWORD hwnd_hi_date_time = GetWindowLong(hwnd, wndExtra - 8);
    DWORD hwnd_lo_date_time = GetWindowLong(hwnd, wndExtra - 4);
    int hwnd_self, hwnd_next;
    hwnd_self = hwnd_hi_date_time - info->self_hi_date_time;
    if (hwnd_self == 0)
      hwnd_self = hwnd_lo_date_time - info->self_lo_date_time;
    hwnd_self *= info->direction;
    hwnd_next = hwnd_hi_date_time - info->next_hi_date_time;
    if (hwnd_next == 0)
      hwnd_next = hwnd_lo_date_time - info->next_lo_date_time;
    hwnd_next *= info->direction;
    if (hwnd_self > 0 && hwnd_next < 0 || (hwnd_self > 0 || hwnd_next < 0)
        && info->next_self <= 0) {
      info->next = hwnd;
      info->next_hi_date_time = hwnd_hi_date_time;
      info->next_lo_date_time = hwnd_lo_date_time;
      info->next_self = hwnd_self;
    }
  }
  return TRUE;
}

static int resizing;

void notify_remote_exit(void *fe)
{
  int exitcode, close_on_exit;

  if (!session_closed && (exitcode = back->exitcode(backhandle)) >= 0) {
    close_on_exit = conf_get_int(conf, CONF_close_on_exit);
    /* Abnormal exits will already have set session_closed and taken
     * appropriate action. */
    if (close_on_exit == FORCE_ON ||
        (close_on_exit == AUTO && exitcode != INT_MAX)) {
      PostQuitMessage(0);
    } else {
      queue_toplevel_callback(close_session, NULL);
      session_closed = TRUE;
      /* exitcode == INT_MAX indicates that the connection was closed
       * by a fatal error, so an error box will be coming our way and
       * we should not generate this informational one. */
      if (exitcode != INT_MAX)
        MessageBox(hwnd, "Connection closed by remote host",
                   appname, MB_OK | MB_ICONINFORMATION);
    }
  }
}

void timer_change_notify(unsigned long next)
{
  unsigned long now = GETTICKCOUNT();
  long ticks;
  if (now - next < INT_MAX)
    ticks = 0;
  else
    ticks = next - now;
  KillTimer(hwnd, TIMING_TIMER_ID);
  SetTimer(hwnd, TIMING_TIMER_ID, ticks, NULL);
  timing_next_time = next;
}

static void conf_cache_data(void)
{
  int key, mod, len;
  char tmp[16];
  char *buf;
  int max, t;

  for (key = 0; key < 256; key++) {
    sprintf(tmp, "VKey%d", key);
    buf = conf_get_str_str(conf, CONF_pvkey_str, tmp);
    max = (buf != NULL) ? strlen(buf) : 0;
    if (!max) {
      for (mod = 0; mod < 8; mod++) {
        pvkey_length[key][mod] = 0;
        pvkey_codes[key][mod][0] = '\0';
      }
      continue;
    }
    t = 0;
    for (mod = 0; mod < 8; mod++) {
      for (len = 0; (t < max) && (buf[t] != ',') && (len < 15); len++, t++) {
        if (buf[t] == '\\') {
          sscanf(&buf[++t], "%03o", &pvkey_codes[key][mod][len]);
          t += 2;
          continue;
        }
        pvkey_codes[key][mod][len] = buf[t];
      }
      pvkey_length[key][mod] = len;
      pvkey_codes[key][mod][len] = '\0';
      t++;
    }
  }

  url_underline = conf_get_int(conf, CONF_url_underline);
  bg_effect = conf_get_int(conf, CONF_bg_effect);
  bg_wallpaper = conf_get_int(conf, CONF_bg_wallpaper);
  wp_position = conf_get_int(conf, CONF_wp_position);
  wp_align = conf_get_int(conf, CONF_wp_align);
  wp_valign = conf_get_int(conf, CONF_wp_valign);
  wp_moving = conf_get_int(conf, CONF_wp_moving);

  baseline_offset = conf_get_int(conf, CONF_baseline_offset);
  baseline_offset_fw = conf_get_int(conf, CONF_baseline_offset_fw);
  border_style = conf_get_int(conf, CONF_border_style);
  cleartype_level = conf_get_int(conf, CONF_cleartype_level);
  enhanced_contrast = conf_get_int(conf, CONF_enhanced_contrast);
  font_quality = conf_get_int(conf, CONF_font_quality);
  gamma = conf_get_int(conf, CONF_gamma);
  line_gap = conf_get_int(conf, CONF_line_gap);
  rendering_mode = conf_get_int(conf, CONF_rendering_mode);
  use_altfont = conf_get_int(conf, CONF_use_altfont);
  use_widefont = conf_get_int(conf, CONF_use_widefont);
  window_border = conf_get_int(conf, CONF_window_border);

  /* Cache some items from conf to speed lookups in very hot code */
  cursor_type = conf_get_int(conf, CONF_cursor_type);
  vtmode = conf_get_int(conf, CONF_vtmode);
}

static LRESULT CALLBACK WndProc(HWND hwnd, UINT message,
                                WPARAM wParam, LPARAM lParam)
{
  HDC hdc;
  static int ignore_clip = FALSE;
  static int need_backend_resize = FALSE;
  static int fullscr_on_max = FALSE;
  static int processed_resize = FALSE;
  static UINT last_mousemove = 0;
  int resize_action;

  switch (message) {
  case WM_TIMER:
    if ((UINT_PTR) wParam == TIMING_TIMER_ID) {
      unsigned long next;

      KillTimer(hwnd, TIMING_TIMER_ID);
      if (run_timers(timing_next_time, &next)) {
        timer_change_notify(next);
      } else {
      }
    /* Reconnect */
    } else if ((UINT_PTR)wParam == TIMING_RECONNECT_ID){
      reconnect();
    }
    return 0;
  case WM_DWMCOMPOSITIONCHANGED:
    bg_glass();
    term_update(term);
    break;
  case WM_WTSSESSION_CHANGE:
    if (wParam == WTS_SESSION_UNLOCK) {
      d2d_init();
    }
    break;
  case WM_CREATE:
    if (conf_get_int(conf, CONF_ctrl_tab_switch)) {
      int wndExtra = GetClassLong(hwnd, GCL_CBWNDEXTRA);
      FILETIME filetime;
      GetSystemTimeAsFileTime(&filetime);
      SetWindowLong(hwnd, wndExtra - 8, filetime.dwHighDateTime);
      SetWindowLong(hwnd, wndExtra - 4, filetime.dwLowDateTime);
    }
    WTSRegisterSessionNotificationEx(WTS_CURRENT_SERVER,
                                     hwnd,
                                     NOTIFY_FOR_THIS_SESSION);
    break;
  case WM_CLOSE:
    {
      char *str;
      show_mouseptr(1);
      str = dupprintf("%s Exit Confirmation", appname);
      if (session_closed || !conf_get_int(conf, CONF_warn_on_close) ||
          MessageBox(hwnd,
                     "Are you sure you want to close this session?",
                     str, MB_ICONWARNING | MB_OKCANCEL | MB_DEFBUTTON1)
          == IDOK)
        DestroyWindow(hwnd);
      sfree(str);
    }
    return 0;
  case WM_DESTROY:
    WTSUnRegisterSessionNotificationEx(WTS_CURRENT_SERVER, hwnd);
    show_mouseptr(1);
    bg_release();
    dw_release();
    d2d_release();
    PostQuitMessage(0);
    return 0;
  case WM_INITMENUPOPUP:
    if ((HMENU) wParam == savedsess_menu) {
      /* About to pop up Saved Sessions sub-menu.
       * Refresh the session list. */
      get_sesslist(&sesslist, FALSE);   /* free */
      get_sesslist(&sesslist, TRUE);
      update_savedsess_menu();
      return 0;
    }
    break;
  case WM_COMMAND:
  case WM_SYSCOMMAND:
    switch (wParam & ~0xF) {    /* low 4 bits reserved to Windows */
    case IDM_SHOWLOG:
      showeventlog(hwnd);
      break;
    case IDM_NEWSESS:
    case IDM_DUPSESS:
    case IDM_SAVEDSESS:
      {
        char b[2048];
        char c[30], *cl;
        int freecl = FALSE;
        BOOL inherit_handles;
        STARTUPINFO si;
        PROCESS_INFORMATION pi;
        HANDLE filemap = NULL;

        if (wParam == IDM_DUPSESS) {
          /*
           * Allocate a file-mapping memory chunk for the
           * config structure.
           */
          SECURITY_ATTRIBUTES sa;
          void *p;
          int size;

          size = conf_serialised_size(conf);

          sa.nLength = sizeof(sa);
          sa.lpSecurityDescriptor = NULL;
          sa.bInheritHandle = TRUE;
          filemap = CreateFileMapping(INVALID_HANDLE_VALUE,
                                      &sa, PAGE_READWRITE, 0, size, NULL);
          if (filemap && filemap != INVALID_HANDLE_VALUE) {
            p = MapViewOfFile(filemap, FILE_MAP_WRITE, 0, 0, size);
            if (p) {
              conf_serialise(conf, p);
              UnmapViewOfFile(p);
            }
          }
          inherit_handles = TRUE;
          sprintf(c, "putty &%p:%u", filemap, (unsigned) size);
          cl = c;
        } else if (wParam == IDM_SAVEDSESS) {
          UINT_PTR sessno = ((lParam - IDM_SAVED_MIN)
                             / MENU_SAVED_STEP) + 1;
          if (sessno < (unsigned) sesslist.nsessions) {
            const char *session = sesslist.sessions[sessno];
            cl = dupprintf("putty @%s", session);
            inherit_handles = FALSE;
            freecl = TRUE;
          } else
            break;
        } else {        /* IDM_NEWSESS */

          cl = NULL;
          inherit_handles = FALSE;
        }

        GetModuleFileName(NULL, b, sizeof(b) - 1);
        si.cb = sizeof(si);
        si.lpReserved = NULL;
        si.lpDesktop = NULL;
        si.lpTitle = NULL;
        si.dwFlags = 0;
        si.cbReserved2 = 0;
        si.lpReserved2 = NULL;
        CreateProcess(b, cl, NULL, NULL, inherit_handles,
                      NORMAL_PRIORITY_CLASS, NULL, NULL, &si, &pi);
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);

        if (filemap)
          CloseHandle(filemap);
        if (freecl)
          sfree(cl);
      }
      break;
    case IDM_RESTART:
      if (!back) {
        logevent(NULL, "----- Session restarted -----");
        term_pwron(term, FALSE);
        start_backend();
      }

      break;
    case IDM_RECONF:
      {
        Conf *prev_conf;
        int init_lvl = 1;
        int reconfig_result;

        if (reconfiguring)
          break;
        else
          reconfiguring = TRUE;

        /*
         * Copy the current window title into the stored
         * previous configuration, so that doing nothing to
         * the window title field in the config box doesn't
         * reset the title to its startup state.
         */
        conf_set_str(conf, CONF_wintitle, window_name);

        prev_conf = conf_copy(conf);

        reconfig_result =
          do_reconfig(hwnd, back ? back->cfg_info(backhandle) : 0);
        reconfiguring = FALSE;
        if (!reconfig_result) {
          conf_free(prev_conf);
          break;
        }

        conf_cache_data();

        resize_action = conf_get_int(conf, CONF_resize_action);
        {
          /* Disable full-screen if resizing forbidden */
          int i;
          for (i = 0; i < lenof(popup_menus); i++)
            EnableMenuItem(popup_menus[i].menu, IDM_FULLSCREEN,
                           MF_BYCOMMAND | (resize_action == RESIZE_DISABLED)
                           ? MF_GRAYED : MF_ENABLED);
          /* Gracefully unzoom if necessary */
          if (IsZoomed(hwnd) && (resize_action == RESIZE_DISABLED))
            ShowWindow(hwnd, SW_RESTORE);
        }

        /* Pass new config data to the logging module */
        log_reconfig(logctx, conf);

        sfree(logpal);
        /*
         * Flush the line discipline's edit buffer in the
         * case where local editing has just been disabled.
         */
        if (ldisc) {
          ldisc_configure(ldisc, conf);
          ldisc_echoedit_update(ldisc);
        }
        if (pal)
          DeleteObject(pal);
        logpal = NULL;
        pal = NULL;
        conftopalette();
        init_palette();

        /* Pass new config data to the terminal */
        term_reconfig(term, conf);

        /* Pass new config data to the back end */
        if (back)
          back->reconfig(backhandle, conf);

        /* Screen size changed ? */
        if (conf_get_int(conf, CONF_height) !=
            conf_get_int(prev_conf, CONF_height) ||
            conf_get_int(conf, CONF_width) !=
            conf_get_int(prev_conf, CONF_width) ||
            conf_get_int(conf, CONF_savelines) !=
            conf_get_int(prev_conf, CONF_savelines) ||
            resize_action == RESIZE_FONT ||
            (resize_action == RESIZE_EITHER && IsZoomed(hwnd)) ||
            resize_action == RESIZE_DISABLED)
          term_size(term, conf_get_int(conf, CONF_height),
                    conf_get_int(conf, CONF_width),
                    conf_get_int(conf, CONF_savelines));

        /* Enable or disable the scroll bar, etc */
        {
          LONG nflg, flag = (LONG) GetWindowLongPtr(hwnd, GWL_STYLE);
          LONG nexflag, exflag = (LONG) GetWindowLongPtr(hwnd, GWL_EXSTYLE);

          nexflag = exflag;
          if (conf_get_int(conf, CONF_alwaysontop) !=
              conf_get_int(prev_conf, CONF_alwaysontop)) {
            if (conf_get_int(conf, CONF_alwaysontop)) {
              nexflag |= WS_EX_TOPMOST;
              SetWindowPos(hwnd, HWND_TOPMOST, 0, 0, 0, 0,
                           SWP_NOMOVE | SWP_NOSIZE);
            } else {
              nexflag &= ~(WS_EX_TOPMOST);
              SetWindowPos(hwnd, HWND_NOTOPMOST, 0, 0, 0, 0,
                           SWP_NOMOVE | SWP_NOSIZE);
            }
          }
          if (conf_get_int(conf, CONF_sunken_edge))
            nexflag |= WS_EX_CLIENTEDGE;
          else
            nexflag &= ~(WS_EX_CLIENTEDGE);

          nflg = flag;
          if (conf_get_int(conf, is_full_screen()?
                           CONF_scrollbar_in_fullscreen : CONF_scrollbar))
            nflg |= WS_VSCROLL;
          else
            nflg &= ~WS_VSCROLL;

          if (resize_action == RESIZE_DISABLED || is_full_screen())
            nflg &= ~WS_THICKFRAME;
          else
            nflg |= WS_THICKFRAME;

          if (resize_action == RESIZE_DISABLED)
            nflg &= ~WS_MAXIMIZEBOX;
          else
            nflg |= WS_MAXIMIZEBOX;

          if (nflg != flag || nexflag != exflag) {
            if (nflg != flag)
              SetWindowLongPtr(hwnd, GWL_STYLE, nflg);
            if (nexflag != exflag)
              SetWindowLongPtr(hwnd, GWL_EXSTYLE, nexflag);

            SetWindowPos(hwnd, NULL, 0, 0, 0, 0,
                         SWP_NOACTIVATE | SWP_NOCOPYBITS |
                         SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER |
                         SWP_FRAMECHANGED);

            init_lvl = 2;
          }
        }

        /* Oops */
        if (resize_action == RESIZE_DISABLED && IsZoomed(hwnd)) {
          force_normal(hwnd);
          init_lvl = 2;
        }

        set_title(NULL, conf_get_str(conf, CONF_wintitle));
        if (IsIconic(hwnd)) {
          SetWindowText(hwnd,
                        conf_get_int(conf, CONF_win_name_always) ?
                        window_name : icon_name);
        }

        {
          FontSpec *font = conf_get_fontspec(conf, CONF_font);
          FontSpec *prev_font = conf_get_fontspec(prev_conf,
                                                  CONF_font);

          if (!strcmp(font->name, prev_font->name) ||
              !strcmp(conf_get_str(conf, CONF_line_codepage),
                      conf_get_str(prev_conf, CONF_line_codepage)) ||
              font->isbold != prev_font->isbold ||
              font->height != prev_font->height ||
              font->charset != prev_font->charset ||
              conf_get_int(conf, CONF_font_quality) !=
              conf_get_int(prev_conf, CONF_font_quality) ||
              conf_get_int(conf, CONF_vtmode) !=
              conf_get_int(prev_conf, CONF_vtmode) ||
              conf_get_int(conf, CONF_bold_style) !=
              conf_get_int(prev_conf, CONF_bold_style) ||
              resize_action == RESIZE_DISABLED ||
              resize_action == RESIZE_EITHER ||
              resize_action != conf_get_int(prev_conf, CONF_resize_action) ||
              conf_get_int(conf, CONF_use_widefont) !=
              conf_get_int(prev_conf, CONF_use_widefont) ||
              conf_get_int(conf, CONF_use_altfont) !=
              conf_get_int(prev_conf, CONF_use_altfont) ||
              strcmp(conf_get_fontspec(conf, CONF_altfont)->name, 
                     conf_get_fontspec(prev_conf, CONF_altfont)->name) != 0)
            init_lvl = 2;
        }

        //d2d
        d2d_init();

        /* Background */
        //d2d
        // bg_init();
        bg_create();

        InvalidateRect(hwnd, NULL, TRUE);
        reset_window(init_lvl);

        conf_free(prev_conf);
      }
      break;
    case IDM_COPYALL:
      term_copyall(term);
      break;
    case IDM_PASTE:
      request_paste(NULL);
      break;
    case IDM_CLRSB:
      term_clrsb(term);
      break;
    case IDM_RESET:
      term_pwron(term, TRUE);
      if (ldisc)
        ldisc_echoedit_update(ldisc);
      break;
    case IDM_ABOUT:
      showabout(hwnd);
      break;
    case IDM_HELP:
      launch_help(hwnd, NULL);
      break;
    case SC_MOUSEMENU:
      /*
       * We get this if the System menu has been activated
       * using the mouse.
       */
      show_mouseptr(1);
      break;
    case SC_KEYMENU:
      /*
       * We get this if the System menu has been activated
       * using the keyboard. This might happen from within
       * TranslateKey, in which case it really wants to be
       * followed by a `space' character to actually _bring
       * the menu up_ rather than just sitting there in
       * `ready to appear' state.
       */
      show_mouseptr(1); /* make sure pointer is visible */
      if (lParam == 0)
        PostMessage(hwnd, WM_CHAR, ' ', 0);
      break;
    case IDM_FULLSCREEN:
      flip_full_screen();
      break;
    default:
      if (wParam >= IDM_SAVED_MIN && wParam < IDM_SAVED_MAX) {
        SendMessage(hwnd, WM_SYSCOMMAND, IDM_SAVEDSESS, wParam);
      }
      if (wParam >= IDM_SPECIAL_MIN && wParam <= IDM_SPECIAL_MAX) {
        INT_PTR i = (wParam - IDM_SPECIAL_MIN) / 0x10;
        /*
         * Ensure we haven't been sent a bogus SYSCOMMAND
         * which would cause us to reference invalid memory
         * and crash. Perhaps I'm just too paranoid here.
         */
        if (i >= n_specials)
          break;
        if (back)
          back->special((void *) backhandle,
                        (Telnet_Special) specials[i].code);

        //d2d
        term_update(term);
      }
    }
    break;

#define X_POS(l) ((int)(short)LOWORD(l))
#define Y_POS(l) ((int)(short)HIWORD(l))

#define TO_CHR_X(x) ((((x)<0 ? (x)-box_width+1 : (x))-offset_width) / box_width)
#define TO_CHR_Y(y) ((((y)<0 ? (y)-box_height+1: (y))-offset_height) / box_height)
  case WM_LBUTTONDOWN:
  case WM_MBUTTONDOWN:
  case WM_RBUTTONDOWN:
  case WM_LBUTTONUP:
  case WM_MBUTTONUP:
  case WM_RBUTTONUP:
    if (message == WM_RBUTTONDOWN &&
        ((wParam & MK_CONTROL) ||
         (conf_get_int(conf, CONF_mouse_is_xterm) == 2))) {
      POINT cursorpos;

      show_mouseptr(1); /* make sure pointer is visible */
      GetCursorPos(&cursorpos);
      TrackPopupMenu(popup_menus[CTXMENU].menu,
                     TPM_LEFTALIGN | TPM_TOPALIGN | TPM_RIGHTBUTTON,
                     cursorpos.x, cursorpos.y, 0, hwnd, NULL);
      break;
    }
    {
      int button, press;

      switch (message) {
      case WM_LBUTTONDOWN:
        button = MBT_LEFT;
        wParam |= MK_LBUTTON;
        press = 1;
        break;
      case WM_MBUTTONDOWN:
        button = MBT_MIDDLE;
        wParam |= MK_MBUTTON;
        press = 1;
        break;
      case WM_RBUTTONDOWN:
        button = MBT_RIGHT;
        wParam |= MK_RBUTTON;
        press = 1;
        break;
      case WM_LBUTTONUP:
        button = MBT_LEFT;
        wParam &= ~MK_LBUTTON;
        press = 0;
        break;
      case WM_MBUTTONUP:
        button = MBT_MIDDLE;
        wParam &= ~MK_MBUTTON;
        press = 0;
        break;
      case WM_RBUTTONUP:
        button = MBT_RIGHT;
        wParam &= ~MK_RBUTTON;
        press = 0;
        break;
      default:
        button = press = 0;     /* shouldn't happen */
      }
      show_mouseptr(1);
      /*
       * Special case: in full-screen mode, if the left
       * button is clicked in the very top left corner of the
       * window, we put up the System menu instead of doing
       * selection.
       */
      {
        char mouse_on_hotspot = 0;
        POINT pt;

        GetCursorPos(&pt);
#ifndef NO_MULTIMON
        {
          HMONITOR mon;
          MONITORINFO mi;

          mon = MonitorFromPoint(pt, MONITOR_DEFAULTTONULL);

          if (mon != NULL) {
            mi.cbSize = sizeof(MONITORINFO);
            GetMonitorInfo(mon, &mi);

            if (mi.rcMonitor.left == pt.x && mi.rcMonitor.top == pt.y) {
              mouse_on_hotspot = 1;
            }
          }
        }
#else
        if (pt.x == 0 && pt.y == 0) {
          mouse_on_hotspot = 1;
        }
#endif
        if (is_full_screen() && press &&
            button == MBT_LEFT && mouse_on_hotspot) {
          SendMessage(hwnd, WM_SYSCOMMAND, SC_MOUSEMENU,
                      MAKELPARAM(pt.x, pt.y));
          return 0;
        }
      }

      if (press) {
        click((Mouse_Button) button,
              TO_CHR_X(X_POS(lParam)), TO_CHR_Y(Y_POS(lParam)),
              wParam & MK_SHIFT, wParam & MK_CONTROL, is_alt_pressed());
        SetCapture(hwnd);
      } else {
        term_mouse(term, (Mouse_Button) button,
                   translate_button((Mouse_Button) button),
                   MA_RELEASE, TO_CHR_X(X_POS(lParam)),
                   TO_CHR_Y(Y_POS(lParam)), wParam & MK_SHIFT,
                   wParam & MK_CONTROL, is_alt_pressed());
        if (!(wParam & (MK_LBUTTON | MK_MBUTTON | MK_RBUTTON)))
          ReleaseCapture();
      }
    }
    return 0;
  case WM_MOUSEMOVE:
    {
      /*
       * Windows seems to like to occasionally send MOUSEMOVE
       * events even if the mouse hasn't moved. Don't unhide
       * the mouse pointer in this case.
       */
      static WPARAM wp = 0;
      static LPARAM lp = 0;
      if (wParam != wp || lParam != lp || last_mousemove != WM_MOUSEMOVE) {
        show_mouseptr(1);
        wp = wParam;
        lp = lParam;
        last_mousemove = WM_MOUSEMOVE;
      }
    }
    /*
     * Add the mouse position and message time to the random
     * number noise.
     */
    noise_ultralight((unsigned long) lParam);

    /* Hyperlink */
    {
      static unsigned long _mouse_on_url = -1;
      int x = TO_CHR_X(X_POS(lParam));
      int y = TO_CHR_Y(Y_POS(lParam));
      unsigned long mouse_on_url =
        (x >= 0) && (x < term->cols) && (y >= 0) && (y < term->rows) ?
        (term->disptext[y]->chars[x].
         attr & TATTR_URLMASK) >> TATTR_URLSHIFT : 0;
      if (_mouse_on_url != mouse_on_url) {
        term_update(term);
        _mouse_on_url = mouse_on_url;
      }
    }

    if (wParam & (MK_LBUTTON | MK_MBUTTON | MK_RBUTTON) &&
        GetCapture() == hwnd) {
      Mouse_Button b;
      if (wParam & MK_LBUTTON)
        b = MBT_LEFT;
      else if (wParam & MK_MBUTTON)
        b = MBT_MIDDLE;
      else
        b = MBT_RIGHT;
      term_mouse(term, b, translate_button(b), MA_DRAG,
                 TO_CHR_X(X_POS(lParam)),
                 TO_CHR_Y(Y_POS(lParam)), wParam & MK_SHIFT,
                 wParam & MK_CONTROL, is_alt_pressed());
    }
    return 0;
  case WM_NCMOUSEMOVE:
    {
      static WPARAM wp = 0;
      static LPARAM lp = 0;
      if (wParam != wp || lParam != lp || last_mousemove != WM_NCMOUSEMOVE) {
        show_mouseptr(1);
        wp = wParam;
        lp = lParam;
        last_mousemove = WM_NCMOUSEMOVE;
      }
    }
    noise_ultralight((unsigned long) lParam);
    break;
  case WM_IGNORE_CLIP:
    ignore_clip = (int) wParam; /* don't panic on DESTROYCLIPBOARD */
    break;
  case WM_DESTROYCLIPBOARD:
    if (!ignore_clip)
      term_deselect(term);
    ignore_clip = FALSE;
    return 0;
  case WM_DISPLAYCHANGE:
  case WM_PAINT:
    {
      PAINTSTRUCT p;
      hdc = BeginPaint(hwnd, &p);
      EndPaint(hwnd, &p);
    }
    return 0;
  case WM_NETEVENT:
        {
          /*
           * To protect against re-entrancy when Windows's recv()
           * immediately triggers a new WSAAsyncSelect window
           * message, we don't call select_result directly from this
           * handler but instead wait until we're back out at the
           * top level of the message loop.
           */
          struct wm_netevent_params *params =
            snew(struct wm_netevent_params);
          params->wParam = wParam;
          params->lParam = lParam;
          queue_toplevel_callback(wm_netevent_callback, params);
        }
    return 0;
  case WM_SETFOCUS:
    term_set_focus(term, TRUE);
    // d2d
    // CreateCaret(hwnd, caretbm, box_width, box_height);
    // ShowCaret(hwnd);
    //
    flash_window(0);    /* stop */
    compose_state = 0;

    /* Background */
    bg_active = BG_ACTIVE;

    term_update(term);
    break;
  case WM_KILLFOCUS:
    show_mouseptr(1);
    term_set_focus(term, FALSE);
    // d2d
    // DestroyCaret();
    //
    caret_x = caret_y = -1;     /* ensure caret is replaced next time */

    /* Background */
    bg_active = BG_INACTIVE;

    term_update(term);
    break;
  case WM_ENTERSIZEMOVE:
#ifdef RDB_DEBUG_PATCH
    debug((27, "WM_ENTERSIZEMOVE"));
#endif
    EnableSizeTip(1);
    resizing = TRUE;
    need_backend_resize = FALSE;
    break;
  case WM_EXITSIZEMOVE:
    EnableSizeTip(0);
    resizing = FALSE;
#ifdef RDB_DEBUG_PATCH
    debug((27, "WM_EXITSIZEMOVE"));
#endif
    if (need_backend_resize) {
      term_size(term, conf_get_int(conf, CONF_height),
                conf_get_int(conf, CONF_width),
                conf_get_int(conf, CONF_savelines));

      //d2d
      // /* Background */
      // bg_resize(1);

      InvalidateRect(hwnd, NULL, TRUE);
    }
    /* Background */
    else {
      bg_move(1);
    }
    break;
  case WM_SIZING:
    /*
     * This does two jobs:
     * 1) Keep the sizetip uptodate
     * 2) Make sure the window size is _stepped_ in units of the font size.
     */
    resize_action = conf_get_int(conf, CONF_resize_action);
    if (resize_action == RESIZE_TERM ||
        (resize_action == RESIZE_EITHER && !is_alt_pressed())) {
      int width, height, w, h, ew, eh;
      LPRECT r = (LPRECT) lParam;

      if (!need_backend_resize && resize_action == RESIZE_EITHER &&
          (conf_get_int(conf, CONF_height) != term->rows ||
           conf_get_int(conf, CONF_width) != term->cols)) {
        /* 
         * Great! It seems that both the terminal size and the
         * font size have been changed and the user is now dragging.
         * 
         * It will now be difficult to get back to the configured
         * font size!
         *
         * This would be easier but it seems to be too confusing.
         */
        conf_set_int(conf, CONF_height, term->rows);
        conf_set_int(conf, CONF_width, term->cols);

        InvalidateRect(hwnd, NULL, TRUE);
        need_backend_resize = TRUE;
      }

      width = r->right - r->left - extra_width;
      height = r->bottom - r->top - extra_height;
      w = (width + box_width / 2) / box_width;
      if (w < 1)
        w = 1;
      h = (height + box_height / 2) / box_height;
      if (h < 1)
        h = 1;
      UpdateSizeTip(hwnd, w, h);
      ew = width - w * box_width;
      eh = height - h * box_height;
      if (ew != 0) {
        if (wParam == WMSZ_LEFT ||
            wParam == WMSZ_BOTTOMLEFT || wParam == WMSZ_TOPLEFT)
          r->left += ew;
        else
          r->right -= ew;
      }
      if (eh != 0) {
        if (wParam == WMSZ_TOP ||
            wParam == WMSZ_TOPRIGHT || wParam == WMSZ_TOPLEFT)
          r->top += eh;
        else
          r->bottom -= eh;
      }
      if (ew || eh)
        return 1;
      else
        return 0;
    } else {
      int width, height, w, h, rv = 0;
      int window_border = conf_get_int(conf, CONF_window_border);
      int ex_width = extra_width + (window_border - offset_width) * 2;
      int ex_height = extra_height + (window_border - offset_height) * 2;
      LPRECT r = (LPRECT) lParam;

      width = r->right - r->left - ex_width;
      height = r->bottom - r->top - ex_height;

      w = (width + term->cols / 2) / term->cols;
      h = (height + term->rows / 2) / term->rows;
      if (r->right != r->left + w * term->cols + ex_width)
        rv = 1;

      if (wParam == WMSZ_LEFT ||
          wParam == WMSZ_BOTTOMLEFT || wParam == WMSZ_TOPLEFT)
        r->left = r->right - w * term->cols - ex_width;
      else
        r->right = r->left + w * term->cols + ex_width;

      if (r->bottom != r->top + h * term->rows + ex_height)
        rv = 1;

      if (wParam == WMSZ_TOP ||
          wParam == WMSZ_TOPRIGHT || wParam == WMSZ_TOPLEFT)
        r->top = r->bottom - h * term->rows - ex_height;
      else
        r->bottom = r->top + h * term->rows + ex_height;

      return rv;
    }
    /* break;  (never reached) */
  case WM_FULLSCR_ON_MAX:
    fullscr_on_max = TRUE;
    break;
  case WM_MOVE:
    {
      RECT rc;
      GetWindowRect(hwnd, &rc);
      conf_set_int(conf, CONF_x, rc.left);
      conf_set_int(conf, CONF_y, rc.top);
    }

    /* Background */
    bg_move(0);

    sys_cursor_update();
    break;
  case WM_SIZE:
    resize_action = conf_get_int(conf, CONF_resize_action);
#ifdef RDB_DEBUG_PATCH
    debug((27, "WM_SIZE %s (%d,%d)",
           (wParam == SIZE_MINIMIZED) ? "SIZE_MINIMIZED" :
           (wParam == SIZE_MAXIMIZED) ? "SIZE_MAXIMIZED" :
           (wParam == SIZE_RESTORED && resizing) ? "to" :
           (wParam == SIZE_RESTORED) ? "SIZE_RESTORED" :
           "...", LOWORD(lParam), HIWORD(lParam)));
#endif
    //d2d
    d2d_resize();
    //
    if (wParam == SIZE_MINIMIZED)
      SetWindowText(hwnd,
                    conf_get_int(conf, CONF_win_name_always) ?
                    window_name : icon_name);
    if (wParam == SIZE_RESTORED || wParam == SIZE_MAXIMIZED)
      SetWindowText(hwnd, window_name);
    if (wParam == SIZE_RESTORED) {
      processed_resize = FALSE;
      clear_full_screen();
      if (processed_resize) {
        /*
         * Inhibit normal processing of this WM_SIZE; a
         * secondary one was triggered just now by
         * clear_full_screen which contained the correct
         * client area size.
         */
        return 0;
      }
    }
    if (wParam == SIZE_MAXIMIZED && fullscr_on_max) {
      fullscr_on_max = FALSE;
      processed_resize = FALSE;
      make_full_screen();
      if (processed_resize) {
        /*
         * Inhibit normal processing of this WM_SIZE; a
         * secondary one was triggered just now by
         * make_full_screen which contained the correct client
         * area size.
         */
        return 0;
      }
    }

    processed_resize = TRUE;

    if (resize_action == RESIZE_DISABLED) {
      /* A resize, well it better be a minimize. */
      reset_window(-1);
    } else {
      int width, height, w, h;
      int window_border = conf_get_int(conf, CONF_window_border);

      width = LOWORD(lParam);
      height = HIWORD(lParam);

      if (wParam == SIZE_MAXIMIZED && !was_zoomed) {
        was_zoomed = 1;
        prev_rows = term->rows;
        prev_cols = term->cols;
        if (resize_action == RESIZE_TERM) {
          w = width / box_width;
          if (w < 1)
            w = 1;
          h = height / box_height;
          if (h < 1)
            h = 1;

          if (resizing) {
            /*
             * As below, if we're in the middle of an
             * interactive resize we don't call
             * back->size. In Windows 7, this case can
             * arise in maximisation as well via the Aero
             * snap UI.
             */
            need_backend_resize = TRUE;
            conf_set_int(conf, CONF_height, h);
            conf_set_int(conf, CONF_width, w);
          } else {
            term_size(term, h, w, conf_get_int(conf, CONF_savelines));
          }
        }
        reset_window(0);
      } else if (wParam == SIZE_RESTORED && was_zoomed) {
        was_zoomed = 0;
        if (resize_action == RESIZE_TERM) {
          w = (width - window_border * 2) / box_width;
          if (w < 1)
            w = 1;
          h = (height - window_border * 2) / box_height;
          if (h < 1)
            h = 1;
          term_size(term, h, w, conf_get_int(conf, CONF_savelines));
          reset_window(2);
        } else if (resize_action != RESIZE_FONT)
          reset_window(2);
        else
          reset_window(0);
      } else if (wParam == SIZE_MINIMIZED) {
        /* do nothing */
      } else if (resize_action == RESIZE_TERM ||
                 (resize_action == RESIZE_EITHER && !is_alt_pressed())) {
        w = (width - window_border * 2) / box_width;
        if (w < 1)
          w = 1;
        h = (height - window_border * 2) / box_height;
        if (h < 1)
          h = 1;

        if (resizing) {
          /*
           * Don't call back->size in mid-resize. (To
           * prevent massive numbers of resize events
           * getting sent down the connection during an NT
           * opaque drag.)
           */
          need_backend_resize = TRUE;
          conf_set_int(conf, CONF_height, h);
          conf_set_int(conf, CONF_width, w);
        } else {
          term_size(term, h, w, conf_get_int(conf, CONF_savelines));
          reset_window(-1);
        }
      } else {
        reset_window(0);
      }
    }
    sys_cursor_update();
    term_update(term);
    return 0;
  case WM_VSCROLL:
    switch (LOWORD(wParam)) {
    case SB_BOTTOM:
      term_scroll(term, -1, 0);
      break;
    case SB_TOP:
      term_scroll(term, +1, 0);
      break;
    case SB_LINEDOWN:
      term_scroll(term, 0, +1);
      break;
    case SB_LINEUP:
      term_scroll(term, 0, -1);
      break;
    case SB_PAGEDOWN:
      term_scroll(term, 0, +term->rows / 2);
      break;
    case SB_PAGEUP:
      term_scroll(term, 0, -term->rows / 2);
      break;
    case SB_THUMBPOSITION:
    case SB_THUMBTRACK:
      /*
       * Use GetScrollInfo instead of HIWORD(wParam) to get
       * 32-bit scroll position.
       */
      {
        SCROLLINFO si;

        si.cbSize = sizeof(si);
        si.fMask = SIF_TRACKPOS;
        if (GetScrollInfo(hwnd, SB_VERT, &si) == 0)
          si.nTrackPos = HIWORD(wParam);
        term_scroll(term, 1, si.nTrackPos);
      }
      break;
    }
    break;
  case WM_PALETTECHANGED:
    if ((HWND) wParam != hwnd && pal != NULL) {
      HDC hdc = get_ctx(NULL);
      if (hdc) {
        if (RealizePalette(hdc) > 0)
          UpdateColors(hdc);
        free_ctx(hdc);
      }
    }
    break;
  case WM_QUERYNEWPALETTE:
    if (pal != NULL) {
      HDC hdc = get_ctx(NULL);
      if (hdc) {
        if (RealizePalette(hdc) > 0)
          UpdateColors(hdc);
        free_ctx(hdc);
        return TRUE;
      }
    }
    return FALSE;
  case WM_KEYDOWN:
  case WM_SYSKEYDOWN:
    if (wParam == VK_TAB && GetKeyState(VK_CONTROL) < 0
        && GetKeyState(VK_MENU) >= 0
        && conf_get_int(conf, CONF_ctrl_tab_switch)) {
      struct ctrl_tab_info info = {
        GetKeyState(VK_SHIFT) < 0 ? 1 : -1,
        hwnd,
      };
      info.next_hi_date_time = info.self_hi_date_time = GetWindowLong(hwnd, 0);
      info.next_lo_date_time = info.self_lo_date_time = GetWindowLong(hwnd, 4);
      EnumWindows(CtrlTabWindowProc, (LPARAM) & info);
      if (info.next != NULL)
        SetForegroundWindow(info.next);
      return 0;
    }
  case WM_KEYUP:
  case WM_SYSKEYUP:
    if (lParam & 0x80000000)
      break;
    /*
     * Add the scan code and keypress timing to the random
     * number noise.
     */
    noise_ultralight((unsigned long) lParam);

    /*
     * We don't do TranslateMessage since it disassociates the
     * resulting CHAR message from the KEYDOWN that sparked it,
     * which we occasionally don't want. Instead, we process
     * KEYDOWN, and call the Win32 translator functions so that
     * we get the translations under _our_ control.
     */
    {
      unsigned char buf[20];
      int len;

      if (wParam == VK_PROCESSKEY || /* IME PROCESS key */
          wParam == VK_PACKET) {     /* 'this key is a Unicode char' */
        if (message == WM_KEYDOWN || message == WM_SYSKEYDOWN) {
          MSG m;
          m.hwnd = hwnd;
          m.message = message;
          m.wParam = wParam;
          m.lParam = lParam & 0xdfff;
          TranslateMessage(&m);
        } else
          break;        /* pass to Windows for default processing */
      } else {
        len = TranslateKey(message, wParam, lParam, buf);
        if (len == -1)
          return DefWindowProcW(hwnd, message, wParam, lParam);

        if (len != 0) {
          /*
           * We need not bother about stdin backlogs
           * here, because in GUI PuTTY we can't do
           * anything about it anyway; there's no means
           * of asking Windows to hold off on KEYDOWN
           * messages. We _have_ to buffer everything
           * we're sent.
           */
          term_seen_key_event(term);
          if (ldisc)
            ldisc_send(ldisc, (char *) buf, len, 1);
          show_mouseptr(0);
        }
      }
    }
    return 0;
  case WM_INPUTLANGCHANGE:
    /* wParam == Font number */
    /* lParam == Locale */
    set_input_locale((HKL) lParam);
    sys_cursor_update();
    {
      HIMC hImc = ImmGetContext(hwnd);
      ime_mode = ImmGetOpenStatus(hImc);
      ImmReleaseContext(hwnd, hImc);
      term_update(term);
    }
    return 1;
  case WM_IME_NOTIFY:
    if (wParam == IMN_SETOPENSTATUS) {
      HIMC hImc = ImmGetContext(hwnd);
      ime_mode = ImmGetOpenStatus(hImc);
      ImmReleaseContext(hwnd, hImc);
      term_update(term);
    }
    break;
  case WM_IME_STARTCOMPOSITION:
    {
      HIMC hImc = ImmGetContext(hwnd);
      ImmSetCompositionFontW(hImc, &lfontw);
      ImmReleaseContext(hwnd, hImc);
    }
    break;
  case WM_IME_COMPOSITION:
    {
      HIMC hIMC;
      int n;
      char *buff;

      if (osVersion.dwPlatformId == VER_PLATFORM_WIN32_WINDOWS ||
          osVersion.dwPlatformId == VER_PLATFORM_WIN32s)
        break;  /* no Unicode */

      if ((lParam & GCS_RESULTSTR) == 0)        /* Composition unfinished. */
        break;  /* fall back to DefWindowProc */

      hIMC = ImmGetContext(hwnd);
      n = ImmGetCompositionStringW(hIMC, GCS_RESULTSTR, NULL, 0);

      if (n > 0) {
        int i;
        buff = snewn(n, char);
        ImmGetCompositionStringW(hIMC, GCS_RESULTSTR, buff, n);
        /*
         * Jaeyoun Chung reports that Korean character
         * input doesn't work correctly if we do a single
         * luni_send() covering the whole of buff. So
         * instead we luni_send the characters one by one.
         */
        term_seen_key_event(term);
        /* don't divide SURROGATE PAIR */
        if (ldisc) {
          for (i = 0; i < n; i += 2) {
            WCHAR hs = *(wchar_t *) (buff + i);
            if (IS_HIGH_SURROGATE(hs) && i + 2 < n) {
              WCHAR ls = *(wchar_t *) (buff + i + 2);
              if (IS_LOW_SURROGATE(ls)) {
                luni_send(ldisc, (wchar_t *) (buff + i), 2, 1);
                i += 2;
                continue;
              }
            }
            luni_send(ldisc, (wchar_t *) (buff + i), 1, 1);
          }
        }
        free(buff);
      }
      ImmReleaseContext(hwnd, hIMC);
      return 1;
    }

  case WM_IME_CHAR:
    if (wParam & 0xFF00) {
      unsigned char buf[2];

      buf[1] = 0xff & wParam;
      buf[0] = 0xff & (wParam >> 8);
      term_seen_key_event(term);
      if (ldisc)
        lpage_send(ldisc, kbd_codepage, (char *) buf, 2, 1);
    } else {
      char c = (unsigned char) wParam;
      term_seen_key_event(term);
      if (ldisc)
        lpage_send(ldisc, kbd_codepage, &c, 1, 1);
    }
    return (0);
  case WM_CHAR:
  case WM_SYSCHAR:
    /*
     * Nevertheless, we are prepared to deal with WM_CHAR
     * messages, should they crop up. So if someone wants to
     * post the things to us as part of a macro manoeuvre,
     * we're ready to cope.
     */
    {
      static wchar_t pending_surrogate = 0;
      wchar_t c = wParam;

      if (IS_HIGH_SURROGATE(c)) {
        pending_surrogate = c;
      } else if (IS_SURROGATE_PAIR(pending_surrogate, c)) {
        wchar_t pair[2];
        pair[0] = pending_surrogate;
        pair[1] = c;
        term_seen_key_event(term);
        luni_send(ldisc, pair, 2, 1);
      } else if (!IS_SURROGATE(c)) {
        term_seen_key_event(term);
        luni_send(ldisc, &c, 1, 1);
      }
    }
    return 0;
  case WM_SYSCOLORCHANGE:
    if (conf_get_int(conf, CONF_system_colour)) {
      /* Refresh palette from system colours. */
      /* XXX actually this zaps the entire palette. */
      systopalette();
      init_palette();
      /* Force a repaint of the terminal window. */
      term_invalidate(term);
    }
    break;
  case WM_AGENT_CALLBACK:
    {
      struct agent_callback *c = (struct agent_callback *) lParam;
      c->callback(c->callback_ctx, c->data, c->len);
      sfree(c);
    }
    return 0;
  case WM_GOT_CLIPDATA:
    if (process_clipdata((HGLOBAL) lParam, (int) wParam))
      term_do_paste(term);
    return 0;
    /* Reconnect */
  case WM_POWERBROADCAST:
    if (conf_get_int(conf, CONF_wakeup_reconnect)) {
      switch (wParam) {
      case PBT_APMRESUMESUSPEND:
      case PBT_APMRESUMEAUTOMATIC:
      case PBT_APMRESUMECRITICAL:
      case PBT_APMQUERYSUSPENDFAILED:
        if (session_closed && !back) {
          reconnect();
        }
        break;
      case PBT_APMSUSPEND:
        if (!session_closed && back) {
          logevent(NULL, "Suspend detected, disconnecting cleanly...");
          close_session(NULL);
        }
        break;
      }
    }
    break;
  case WM_IME_REQUEST:
    switch (wParam) {
    case IMR_DOCUMENTFEED:
      {
        RECONVERTSTRING *re = (RECONVERTSTRING *) lParam;
        int size = term->cols;
        if (size > 511) {
          size = 511;
        }
        if (re) {
          int i;
          unsigned long uc;
          int c = 0;
          char *str = (char *) re + sizeof(RECONVERTSTRING);

          for (i = 0; i < size; i++) {
            uc = term->disptext[term->dispcursy]->chars[i].chr;
            if ((uc == UCSWIDE) || DIRECT_CHAR(uc)) {
              continue;
            }
            if (DIRECT_FONT(uc)) {
              uc &= ~CSET_MASK;
            }
            ime_w[c++] = (wchar_t) uc;
          }
          ime_w[c] = L'\0';
          size++;
          WideCharToMultiByte(CP_ACP, 0, ime_w, -1, ime_m, size, NULL, NULL);

          re->dwSize = sizeof(RECONVERTSTRING) + size;
          re->dwVersion = 0;
          re->dwStrLen = size;
          re->dwStrOffset = sizeof(RECONVERTSTRING);
          re->dwCompStrLen = 0;
          re->dwCompStrOffset = 0;
          re->dwTargetStrLen = 0;
          re->dwTargetStrOffset = term->dispcursx;
          memcpy((void *) str, (void *) ime_m, size);
        } else {
          size++;
        }
        return sizeof(RECONVERTSTRING) + size;
      }
    }
    break;
  case WM_ERASEBKGND:
    return FALSE;
  case WM_NOTIFY_RECONNECT:
    reconnect();
    break;
  default:
    if (message == wm_mousewheel || message == WM_MOUSEWHEEL) {
      int shift_pressed = 0, control_pressed = 0;

      if (message == WM_MOUSEWHEEL) {
        wheel_accumulator += (short) HIWORD(wParam);
        shift_pressed = LOWORD(wParam) & MK_SHIFT;
        control_pressed = LOWORD(wParam) & MK_CONTROL;
      } else {
        BYTE keys[256];
        wheel_accumulator += (int) wParam;
        if (GetKeyboardState(keys) != 0) {
          shift_pressed = keys[VK_SHIFT] & 0x80;
          control_pressed = keys[VK_CONTROL] & 0x80;
        }
      }

      /* process events when the threshold is reached */
      while (abs(wheel_accumulator) >= WHEEL_DELTA) {
        Mouse_Button b;

        /* reduce amount for next time */
        if (wheel_accumulator > 0) {
          b = MBT_WHEEL_UP;
          wheel_accumulator -= WHEEL_DELTA;
        } else if (wheel_accumulator < 0) {
          b = MBT_WHEEL_DOWN;
          wheel_accumulator += WHEEL_DELTA;
        } else
          break;

        if (send_raw_mouse &&
            !(conf_get_int(conf, CONF_mouse_override) && shift_pressed)) {
          /* Mouse wheel position is in screen coordinates for
           * some reason */
          POINT p;
          p.x = X_POS(lParam);
          p.y = Y_POS(lParam);
          if (ScreenToClient(hwnd, &p)) {
            /* send a mouse-down followed by a mouse up */
            term_mouse(term, b, translate_button(b),
                       MA_CLICK,
                       TO_CHR_X(p.x),
                       TO_CHR_Y(p.y), shift_pressed,
                       control_pressed, is_alt_pressed());
          }     /* else: not sure when this can fail */
        } else {
          /* trigger a scroll */
          term_scroll(term, 0,
                      b == MBT_WHEEL_UP ? -term->rows / 2 : term->rows / 2);
        }
      }
      return 0;
    }
  }

  /*
   * Any messages we don't process completely above are passed through to
   * DefWindowProc() for default processing.
   */
  return DefWindowProcW(hwnd, message, wParam, lParam);
}

/*
 * Move the system caret. (We maintain one, even though it's
 * invisible, for the benefit of blind people: apparently some
 * helper software tracks the system caret, so we should arrange to
 * have one.)
 */
void sys_cursor(void *frontend, int x, int y)
{
  int cx, cy;

  if (!term->has_focus)
    return;

  /*
   * Avoid gratuitously re-updating the cursor position and IMM
   * window if there's no actual change required.
   */
  cx = x * box_width + offset_width;
  //d2d
  // cy = y * box_height + offset_height;
  cy = y * box_height + offset_height + line_gap - baseline_offset_fw;
  if (cx == caret_x && cy == caret_y)
    return;
  caret_x = cx;
  caret_y = cy;

  sys_cursor_update();
}

static void sys_cursor_update(void)
{
  COMPOSITIONFORM cf;
  HIMC hIMC;

  if (!term->has_focus)
    return;

  if (caret_x < 0 || caret_y < 0)
    return;

  SetCaretPos(caret_x, caret_y);

  /* IMM calls on Win98 and beyond only */
  if (osVersion.dwPlatformId == VER_PLATFORM_WIN32s)
    return;     /* 3.11 */

  if (osVersion.dwPlatformId == VER_PLATFORM_WIN32_WINDOWS &&
      osVersion.dwMinorVersion == 0)
    return;     /* 95 */

  /* we should have the IMM functions */
  hIMC = ImmGetContext(hwnd);
  cf.dwStyle = CFS_POINT;
  cf.ptCurrentPos.x = caret_x;
  cf.ptCurrentPos.y = caret_y;
  ImmSetCompositionWindow(hIMC, &cf);

  ImmReleaseContext(hwnd, hIMC);
}

/*
 * Draw a line of text in the window, at given character
 * coordinates, in given attributes.
 *
 * We are allowed to fiddle with the contents of `text'.
 */
void do_text_internal(Context ctx, int x, int y, wchar_t * text, int len,
                      unsigned long long attr, int lattr)
{
  COLORREF fg, bg, t;
  int nfg, nbg, nfont;
  HDC hdc = ctx;
  RECT line_box;
  int force_manual_underline = 0;
  int fnt_width, char_width;
  int text_adjust = 0;
  int xoffset = 0;
  int maxlen, remaining, opaque;
  int is_cursor = FALSE;
  static int *lpDx = NULL;
  static int lpDx_len = 0;
  int *lpDx_maybe;
  int len2;     /* for SURROGATE PAIR */

  // d2d
  // CHAR sM[1024];
  // WideCharToMultiByte(CP_UTF8, 0, (LPCWSTR)text, len, (LPSTR)sM, 256, NULL,    NULL);
  // printf("dti: x=%d y=%d len=%d text='%s'\n",
  //        x, y, len, sM);
  //

  /* Hyperlink */
  {
    POINT pt;
    int ms_x;
    int ms_y;

    GetCursorPos(&pt);
    ScreenToClient(hwnd, &pt);
    ms_x = TO_CHR_X(pt.x);
    ms_y = TO_CHR_Y(pt.y);

    if ((attr & TATTR_URLMASK) &&
        ((url_underline == URL_UNDERLINE_ALWAYS) ||
         ((url_underline == URL_UNDERLINE_HOVER) &&
          (ms_x >= 0) && (ms_x < term->cols) &&
          (ms_y >= 0) && (ms_y < term->rows) &&
          ((term->disptext[ms_y]->chars[ms_x].attr & TATTR_URLMASK) ==
           (attr & TATTR_URLMASK))))) {
      attr |= ATTR_UNDER;
    }
  }

  lattr &= LATTR_MODE;

  char_width = fnt_width = box_width * (1 + (lattr != LATTR_NORM));

  if (attr & ATTR_WIDE)
    char_width *= 2;

  /* Only want the left half of double width lines */
  if (lattr != LATTR_NORM && x * 2 >= term->cols)
    return;

  x *= fnt_width;
  y *= box_height;
  x += offset_width;
  y += offset_height;

  if ((attr & TATTR_ACTCURS) && (cursor_type == 0 || term->big_cursor)) {
    attr &= ~(ATTR_REVERSE | ATTR_BLINK | ATTR_COLOURS);
    /* cursor fg and bg */
    if (ime_mode)
      attr |= (262 << ATTR_FGSHIFT) | (263 << ATTR_BGSHIFT);
    else
      attr |= (260 << ATTR_FGSHIFT) | (261 << ATTR_BGSHIFT);
    is_cursor = TRUE;
  }

  nfont = 0;
  if (vtmode == VT_POORMAN && lattr != LATTR_NORM) {
    /* Assume a poorman font is borken in other ways too. */
    lattr = LATTR_WIDE;
  } else
    switch (lattr) {
    case LATTR_NORM:
      break;
    case LATTR_WIDE:
      nfont |= FONT_WIDE;
      break;
    default:
      nfont |= FONT_WIDE + FONT_HIGH;
      break;
    }
  if (attr & ATTR_NARROW)
    nfont |= FONT_NARROW;

#ifdef USES_VTLINE_HACK
  /* Special hack for the VT100 linedraw glyphs. */
  if (text[0] >= 0x23BA && text[0] <= 0x23BD) {
    switch ((unsigned char) (text[0])) {
    case 0xBA:
      text_adjust = -2 * box_height / 5;
      break;
    case 0xBB:
      text_adjust = -1 * box_height / 5;
      break;
    case 0xBC:
      text_adjust = box_height / 5;
      break;
    case 0xBD:
      text_adjust = 2 * box_height / 5;
      break;
    }
    if (lattr == LATTR_TOP || lattr == LATTR_BOT)
      text_adjust *= 2;
    text[0] = ucsdata.unitab_xterm['q'];
    if (attr & ATTR_UNDER) {
      attr &= ~ATTR_UNDER;
      force_manual_underline = 1;
    }
  }
#endif

  /* Anything left as an original character set is unprintable. */
  if (DIRECT_CHAR(text[0]) &&
      (len < 2 || !IS_SURROGATE_PAIR(text[0], text[1]))) {
    int i;
    for (i = 0; i < len; i++)
      text[i] = 0xFFFD;
  }

  /* OEM CP */
  if ((text[0] & CSET_MASK) == CSET_OEMCP)
    nfont |= FONT_OEM;

  nfg = ((attr & ATTR_FGMASK) >> ATTR_FGSHIFT);
  nbg = ((attr & ATTR_BGMASK) >> ATTR_BGSHIFT);
  if (bold_font_mode == BOLD_FONT && (attr & ATTR_BOLD))
    nfont |= FONT_BOLD;
  if (und_mode == UND_FONT && (attr & ATTR_UNDER))
    nfont |= FONT_UNDERLINE;
  //d2d
  // another_font(nfont);
  // if (!fonts[nfont]) {
  //   if (nfont & FONT_UNDERLINE)
  //     force_manual_underline = 1;
  //   /* Don't do the same for manual bold, it could be bad news. */

  //   nfont &= ~(FONT_BOLD | FONT_UNDERLINE);
  // }
  // another_font(nfont);
  if (!fonts[nfont])
    nfont = FONT_NORMAL;
  if (attr & ATTR_REVERSE) {
    t = nfg;
    nfg = nbg;
    nbg = t;
  }
  if (bold_colours && (attr & ATTR_BOLD) && !is_cursor) {
    if (nfg < 16)
      nfg |= 8;
    else if (nfg >= 256)
      nfg |= 1;
  }
  if (bold_colours && (attr & ATTR_BLINK)) {
    if (nbg < 16)
      nbg |= 8;
    else if (nbg >= 256)
      nbg |= 1;
  }
  fg = colours[nfg];
  bg = colours[nbg];
  SelectObject(hdc, fonts[nfont]);
  //d2d
  // SetTextColor(hdc, fg);
  // SetBkColor(hdc, bg);
  /* > transparent background patch */
  // if ((cfg.transparent_mode & 3) && (nbg == 258)) {
  //   SetBkMode(hdc, TRANSPARENT);
  //   (*xtrans_paint_background)(hdc, x, y, char_width * len, box_height);
  // } else {
  //   /* < */
  //   if (attr & TATTR_COMBINING)
  //     SetBkMode(hdc, TRANSPARENT);
  //   else
  //     SetBkMode(hdc, OPAQUE);
  //   /* > transparent background patch */
  // }
  /* < */
  // SetBkMode(hdc, TRANSPARENT);
  if (d2dSCBfg) {
    // d2dSCBfg->SetColor(D2D1::ColorF(1.0f, 0.0f, 0.0f, 0.8f));
    // d2dSCBbg->SetColor(D2D1::ColorF(0.0f, 0.0f, 1.0f, 0.1f));
    d2dSCBfg->
      SetColor(D2D1::
               ColorF(colours[nfg], alphas[ALPHA_DEFAULT_FG][bg_active]));

    //!!!
    d2dSCBbg->SetColor(D2D1::ColorF(colours[nbg],
                                    (nbg ==
                                     258) ? alphas[ALPHA_DEFAULT_BG][bg_active]
                                    : alphas[ALPHA_BG][bg_active]));
    // d2dSCBbg->SetColor(
    //   D2D1::ColorF(colours[nbg],
    //                (nbg == 258) ? 0.0f :
    //                               alphas[ALPHA_BG][BG_ACTIVE]));
    opaque = (nbg == 258) ? 0 : 1;
  }
  //
  line_box.left = x;
  line_box.top = y;
  line_box.right = x + char_width * len;
  line_box.bottom = y + box_height;
  /* adjust line_box.right for SURROGATE PAIR & VARIATION SELECTOR */
  {
    int i;
    int rc_width = 0;
    for (i = 0; i < len; i++) {
      if (i + 1 < len && IS_HIGH_VARSEL(text[i], text[i + 1])) {
        i++;
      } else if (i + 1 < len && IS_SURROGATE_PAIR(text[i], text[i + 1])) {
        rc_width += char_width;
        i++;
      } else if (IS_LOW_VARSEL(text[i])) {
        /* do nothing */
      } else {
        rc_width += char_width;
      }
    }
    line_box.right = line_box.left + rc_width;
  }

  /* Only want the left half of double width lines */
  if (line_box.right > box_width * term->cols + offset_width)
    line_box.right = box_width * term->cols + offset_width;

  /*
   * In a fixed-pitch font, we draw the whole string in one go
   * in the normal way.
   */
  xoffset = 0;
  //d2d
  // SetTextAlign(hdc, TA_TOP | TA_LEFT | TA_NOUPDATECP);
  lpDx_maybe = lpDx;
  maxlen = len;

  //d2d
  // opaque = TRUE;        /* start by erasing the rectangle */
  for (remaining = len; remaining > 0;
       text += len, remaining -= len, x += char_width * len2) {
    len = (maxlen < remaining ? maxlen : remaining);
    /* don't divide SURROGATE PAIR and VARIATION SELECTOR */
    len2 = len;
    if (maxlen == 1) {
      if (remaining >= 1 && IS_SURROGATE_PAIR(text[0], text[1]))
        len++;
      if (remaining - len >= 1 && IS_LOW_VARSEL(text[len]))
        len++;
      else if (remaining - len >= 2 &&
               IS_HIGH_VARSEL(text[len], text[len + 1]))
        len += 2;
    }

    if (len > lpDx_len) {
      lpDx_len = len * 9 / 8 + 16;
      lpDx = sresize(lpDx, lpDx_len, int);

      if (lpDx_maybe)
        lpDx_maybe = lpDx;
    }

    {
      int i;
      /* only last char has dx width in SURROGATE PAIR and
       * VARIATION sequence */
      for (i = 0; i < len; i++) {
        lpDx[i] = char_width;
        if (i + 1 < len && IS_HIGH_VARSEL(text[i], text[i + 1])) {
          if (i > 0)
            lpDx[i - 1] = 0;
          lpDx[i] = 0;
          i++;
          lpDx[i] = char_width;
        } else if (i + 1 < len && IS_SURROGATE_PAIR(text[i], text[i + 1])) {
          lpDx[i] = 0;
          i++;
          lpDx[i] = char_width;
        } else if (IS_LOW_VARSEL(text[i])) {
          if (i > 0)
            lpDx[i - 1] = 0;
          lpDx[i] = char_width;
        }
      }
    }

    /* We're using a private area for direct to font. (512 chars.) */
    if (ucsdata.dbcs_screenfont && (text[0] & CSET_MASK) == CSET_ACP) {
      /* Ho Hum, dbcs fonts are a PITA! */
      /* To display on W9x I have to convert to UCS */
      static wchar_t *uni_buf = 0;
      static int uni_len = 0;
      int nlen, mptr;
      if (len > uni_len) {
        sfree(uni_buf);
        uni_len = len;
        uni_buf = snewn(uni_len, wchar_t);
      }

      for (nlen = mptr = 0; mptr < len; mptr++) {
        uni_buf[nlen] = 0xFFFD;
        if (IsDBCSLeadByteEx(ucsdata.font_codepage, (BYTE) text[mptr])) {
          char dbcstext[2];
          dbcstext[0] = text[mptr] & 0xFF;
          dbcstext[1] = text[mptr + 1] & 0xFF;
          lpDx[nlen] += char_width;
          MultiByteToWideChar(ucsdata.font_codepage, MB_USEGLYPHCHARS,
                              dbcstext, 2, uni_buf + nlen, 1);
          mptr++;
        } else {
          char dbcstext[1];
          dbcstext[0] = text[mptr] & 0xFF;
          MultiByteToWideChar(ucsdata.font_codepage, MB_USEGLYPHCHARS,
                              dbcstext, 1, uni_buf + nlen, 1);
        }
        nlen++;
      }
      if (nlen <= 0)
        return; /* Eeek! */

      //d2d
      // ExtTextOutW2(!!(attr & ATTR_WIDE), hdc, x + xoffset,
      //              y - box_height * (lattr == LATTR_BOT) + text_adjust,
      //              ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
      //              &line_box, uni_buf, nlen, lpDx_maybe);
      dw_textout(x + xoffset,
                 y - box_height * (lattr == LATTR_BOT) + text_adjust,
                 ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
                 &line_box, uni_buf, nlen, lpDx, !!(attr & ATTR_WIDE), attr);
      //d2d
      // if (bold_font_mode == BOLD_SHADOW && (attr & ATTR_BOLD)) {
      //   SetBkMode(hdc, TRANSPARENT);
      //   ExtTextOutW2(!!(attr & ATTR_WIDE), hdc, x + xoffset - 1,
      //                y - box_height * (lattr ==
      //                                   LATTR_BOT) + text_adjust,
      //                ETO_CLIPPED, &line_box, uni_buf, nlen, lpDx_maybe);
      // }

      lpDx[0] = -1;
    //d2d
    // } else if (DIRECT_FONT(text[0])) {
    //   static char *directbuf = NULL;
    //   static int directlen = 0;
    //   int i;
    //   if (len > directlen) {
    //     directlen = len;
    //     directbuf = sresize(directbuf, directlen, char);
    //   }

    //   for (i = 0; i < len; i++)
    //     directbuf[i] = text[i] & 0xFF;

    //   ExtTextOut(hdc, x + xoffset,
    //              y - box_height * (lattr == LATTR_BOT) + text_adjust,
    //              ETO_CLIPPED | (opaque ? ETO_OPAQUE : 0),
    //              &line_box, directbuf, len, lpDx_maybe);
    //   if (bold_font_mode == BOLD_SHADOW && (attr & ATTR_BOLD)) {
    //     SetBkMode(hdc, TRANSPARENT);

    //     /* GRR: This draws the character outside its box and
    //      * can leave 'droppings' even with the clip box! I
    //      * suppose I could loop it one character at a time ...
    //      * yuk.
    //      * 
    //      * Or ... I could do a test print with "W", and use +1
    //      * or -1 for this shift depending on if the leftmost
    //      * column is blank...
    //      */
    //     ExtTextOut(hdc, x + xoffset - 1,
    //                y - box_height * (lattr ==
    //                                   LATTR_BOT) + text_adjust,
    //                ETO_CLIPPED, &line_box, directbuf, len, lpDx_maybe);
    //   }
    } else {
      /* And 'normal' unicode characters */
      static WCHAR *wbuf = NULL;
      static int wlen = 0;
      int i;

      if (wlen < len) {
        sfree(wbuf);
        wlen = len;
        wbuf = snewn(wlen, WCHAR);
      }

      //d2d
      // for (i = 0; i < len; i++)
      //   wbuf[i] = text[i];
      for (i = 0; i < len; i++) {
        wbuf[i] = (DIRECT_FONT(text[0])) ? text[i] & 0xFF : text[i];
      }

      /* print Glyphs as they are, without Windows' Shaping */
      //d2d
      // general_textout(hdc, x + xoffset,
      //                 y - box_height * (lattr == LATTR_BOT) + text_adjust,
      //                 &line_box, wbuf, len, lpDx,
      //                 opaque && !(attr & TATTR_COMBINING),
      //                 (attr & ATTR_WIDE) ? ExtTextOutW2wide
      //                 : ExtTextOutW2narrow);

      // /* And the shadow bold hack. */
      // if (bold_font_mode == BOLD_SHADOW && (attr & ATTR_BOLD)) {
      //   SetBkMode(hdc, TRANSPARENT);
      //   ExtTextOutW2(!!(attr & ATTR_WIDE), hdc, x + xoffset - 1,
      //                y - box_height * (lattr ==
      //                                   LATTR_BOT) + text_adjust,
      //                ETO_CLIPPED, &line_box, wbuf, len, lpDx_maybe);
      // }
      general_textout2(hdc, x + xoffset,
                       y - box_height * (lattr == LATTR_BOT) + text_adjust,
                       &line_box, (unsigned short *) wbuf, len, lpDx,
                       opaque && !(attr & TATTR_COMBINING),
                       !!(attr & ATTR_WIDE),
                       in_utf(term) && term->ucsdata->iso2022, attr);
    }

    /*
     * If we're looping round again, stop erasing the background
     * rectangle.
     */
    //d2d
    // SetBkMode(hdc, TRANSPARENT);
    opaque = FALSE;
  }
  //d2d
  // if (lattr != LATTR_TOP && (force_manual_underline ||
  //                            (und_mode == UND_LINE && (attr & ATTR_UNDER)))) {
  //   HPEN oldpen;
  //   int dec = descent;
  //   if (lattr == LATTR_BOT)
  //     dec = dec * 2 - box_height;

  //   oldpen = SelectObject(hdc, CreatePen(PS_SOLID, 0, fg));
  //   MoveToEx(hdc, line_box.left, line_box.top + dec, NULL);
  //   LineTo(hdc, line_box.right, line_box.top + dec);
  //   oldpen = SelectObject(hdc, oldpen);
  //   DeleteObject(oldpen);
  // }
}

/*
 * Wrapper that handles combining characters.
 */
void do_text(Context ctx, int x, int y, wchar_t * text, int len,
             unsigned long long attr, int lattr)
{
  if (attr & TATTR_COMBINING) {
    unsigned long a = 0;
    int len0 = 1;
    /* don't divide SURROGATE PAIR and VARIATION SELECTOR */
    if (len >= 2 && IS_SURROGATE_PAIR(text[0], text[1]))
      len0 = 2;
    if (len - len0 >= 1 && IS_LOW_VARSEL(text[len0])) {
      attr &= ~TATTR_COMBINING;
      do_text_internal(ctx, x, y, text, len0 + 1, attr, lattr);
      text += len0 + 1;
      len -= len0 + 1;
      a = TATTR_COMBINING;
    } else if (len - len0 >= 2 && IS_HIGH_VARSEL(text[len0], text[len0 + 1])) {
      attr &= ~TATTR_COMBINING;
      do_text_internal(ctx, x, y, text, len0 + 2, attr, lattr);
      text += len0 + 2;
      len -= len0 + 2;
      a = TATTR_COMBINING;
    } else {
      attr &= ~TATTR_COMBINING;
    }

    while (len--) {
      if (len >= 1 && IS_SURROGATE_PAIR(text[0], text[1])) {
        do_text_internal(ctx, x, y, text, 2, attr | a, lattr);
        len--;
        text++;
      } else {
        do_text_internal(ctx, x, y, text, 1, attr | a, lattr);
      }

      text++;
      a = TATTR_COMBINING;
    }
  } else {
    do_text_internal(ctx, x, y, text, len, attr, lattr);
  }
}

void do_cursor(Context ctx, int x, int y, wchar_t * text, int len,
               unsigned long long attr, int lattr)
{
  // D2DBG("do_cursor: len=%d attr=%x lattr=%x\n", len, attr, lattr);

  int fnt_width;
  int char_width;
  HDC hdc = ctx;
  int ctype = cursor_type;

  lattr &= LATTR_MODE;

  if ((attr & TATTR_ACTCURS) && (ctype == 0 || term->big_cursor)) {
    if (*text != UCSWIDE) {
      do_text(ctx, x, y, text, len, attr, lattr);
      return;
    }
    ctype = 2;
    attr |= TATTR_RIGHTCURS;
  }

  fnt_width = char_width = box_width * (1 + (lattr != LATTR_NORM));
  if (attr & ATTR_WIDE)
    char_width *= 2;
  x *= fnt_width;
  y *= box_height;
  x += offset_width;
  y += offset_height;

  //d2d
  d2dSCBc->SetColor(D2D1::ColorF(ime_mode ? colours[263] : colours[261],
                                 alphas[ALPHA_CURSOR][bg_active]));

  if ((attr & TATTR_PASCURS) && (ctype == 0 || term->big_cursor)) {
    //d2d
    D2D1_RECT_F r = D2D1::RectF((FLOAT) x,
                                (FLOAT) y,
                                (FLOAT) x + char_width - 1,
                                (FLOAT) y + box_height - 1);
    d2dRT->DrawRectangle(&r, d2dSCBc);
    // POINT pts[5];
    // HPEN oldpen;
    // pts[0].x = pts[1].x = pts[4].x = x;
    // pts[2].x = pts[3].x = x + char_width - 1;
    // pts[0].y = pts[3].y = pts[4].y = y;
    // pts[1].y = pts[2].y = y + box_height - 1;
    // oldpen = (HPEN)SelectObject(hdc, CreatePen(PS_SOLID, 0, colour));
    // Polyline(hdc, pts, 5);
    // oldpen = (HPEN)SelectObject(hdc, oldpen);
    // DeleteObject(oldpen);
  } else if ((attr & (TATTR_ACTCURS | TATTR_PASCURS)) && ctype != 0) {
    int startx, starty, dx, dy, length;
    if (ctype == 1) {
      startx = x;
      starty = y + descent;
      dx = 1;
      dy = 0;
      length = char_width;
    } else {
      int xadjust = 0;
      if (attr & TATTR_RIGHTCURS)
        xadjust = char_width - 1;
      startx = x + xadjust;
      starty = y;
      dx = 0;
      dy = 1;
      length = box_height;
    }
    if (attr & TATTR_ACTCURS) {
      // d2d
      d2dRT->DrawLine(D2D1::Point2F((FLOAT) startx, (FLOAT) starty),
                      D2D1::Point2F((FLOAT) startx + dx * length,
                                    (FLOAT) starty + dy * length),
                      d2dSCBc, 2.0f);
      // HPEN oldpen;
      // oldpen = (HPEN)SelectObject(hdc, CreatePen(PS_SOLID, 0, colour));
      // MoveToEx(hdc, startx, starty, NULL);
      // LineTo(hdc, startx + dx * length, starty + dy * length);
      // oldpen = (HPEN)SelectObject(hdc, oldpen);
      // DeleteObject(oldpen);
    } else {
      // d2d
      d2dRT->DrawLine(D2D1::Point2F((FLOAT) startx, (FLOAT) starty),
                      D2D1::Point2F((FLOAT) startx + dx * length,
                                    (FLOAT) starty + dy * length),
                      d2dSCBc, 2.0f, d2dSS);
      // for (i = 0; i < length; i++) {
      //   if (i % 2 == 0) {
      //     SetPixel(hdc, startx, starty, colour);
      //   }
      //   startx += dx;
      //   starty += dy;
      // }
    }
  }
}

/* This function gets the actual width of a character in the normal font.
 */
int char_width(Context ctx, int uc)
{
  //d2d
  return 1;

  if ((uc & ~CSET_MASK) == ' ')
    return 1;
  // D2DBG("char_width: uc=%x, ", uc);
  //

  HDC hdc = ctx;
  int ibuf = 0;

  /* If the font max is the same as the font ave width then this
   * function is a no-op.
   */
  if (!font_dualwidth) {
    return 1;
  }

  switch (uc & CSET_MASK) {
  case CSET_ASCII:{
      uc = ucsdata.unitab_line[uc & 0xFF];
      break;
    }
  case CSET_LINEDRW:
    uc = ucsdata.unitab_xterm[uc & 0xFF];
    break;
  case CSET_SCOACS:
    uc = ucsdata.unitab_scoacs[uc & 0xFF];
    break;
  }
  if (DIRECT_FONT(uc)) {
    if (ucsdata.dbcs_screenfont) {
      return 1;
    }

    /* Speedup, I know of no font where ascii is the wrong width */
    if ((uc & ~CSET_MASK) >= ' ' && (uc & ~CSET_MASK) <= '~') {
      return 1;
    }

    if ((uc & CSET_MASK) == CSET_ACP) {
      SelectObject(hdc, fonts[FONT_NORMAL]);
    } else if ((uc & CSET_MASK) == CSET_OEMCP) {
      another_font(FONT_OEM);
      if (!fonts[FONT_OEM]) {
        return 0;
      }
      SelectObject(hdc, fonts[FONT_OEM]);
    } else {
      return 0;
    }

    if (GetCharWidth32(hdc, uc & ~CSET_MASK, uc & ~CSET_MASK, &ibuf) != 1 &&
        GetCharWidth(hdc, uc & ~CSET_MASK, uc & ~CSET_MASK, &ibuf) != 1) {
      return 0;
    }
  } else {
    /* Speedup, I know of no font where ascii is the wrong width */
    if (uc >= ' ' && uc <= '~') {
      return 1;
    }

    SelectObject(hdc, fonts[FONT_NORMAL]);
    if (GetCharWidth32W(hdc, uc, uc, &ibuf) == 1) {
      /* Okay that one worked */ ;
    } else if (GetCharWidthW(hdc, uc, uc, &ibuf) == 1) {
      /* This should work on 9x too, but it's "less accurate" */ ;
    } else {
      return 0;
    }
  }

  ibuf += box_width / 2 - 1;
  ibuf /= box_width;

  return ibuf;
}

DECL_WINDOWS_FUNCTION(static, BOOL, FlashWindowEx, (PFLASHWINFO));
DECL_WINDOWS_FUNCTION(static, BOOL, ToUnicodeEx,
                      (UINT, UINT, const BYTE *, LPWSTR, int, UINT, HKL));

static void init_winfuncs(void)
{
  HMODULE user32_module = load_system32_dll("user32.dll");
  GET_WINDOWS_FUNCTION(user32_module, FlashWindowEx);
  GET_WINDOWS_FUNCTION(user32_module, ToUnicodeEx);
}

/*
 * Translate a WM_(SYS)?KEY(UP|DOWN) message into a string of ASCII
 * codes. Returns number of bytes used, zero to drop the message,
 * -1 to forward the message to Windows, or another negative number
 * to indicate a NUL-terminated "special" string.
 */
static int TranslateKey(UINT message, WPARAM wParam, LPARAM lParam,
                        unsigned char *output)
{
  BYTE keystate[256];
  int scan, left_alt = 0, key_down, shift_state;
  int r, i, code;
  unsigned char *p = output;
  static int alt_sum = 0;
  int funky_type = conf_get_int(conf, CONF_funky_type);
  int no_applic_k = conf_get_int(conf, CONF_no_applic_k);
  int ctrlaltkeys = conf_get_int(conf, CONF_ctrlaltkeys);
  int nethack_keypad = conf_get_int(conf, CONF_nethack_keypad);
  int rightaltkey = conf_get_int(conf, CONF_rightaltkey);

  HKL kbd_layout = GetKeyboardLayout(0);

  static wchar_t keys_unicode[3];
  static int compose_char = 0;
  static WPARAM compose_keycode = 0;

  r = GetKeyboardState(keystate);
  if (!r)
    memset(keystate, 0, sizeof(keystate));
  else {
#if 0
#define SHOW_TOASCII_RESULT
    {			       /* Tell us all about key events */
	    static BYTE oldstate[256];
	    static int first = 1;
	    static int scan;
	    int ch;
	    if (first)
        memcpy(oldstate, keystate, sizeof(oldstate));
	    first = 0;

	    if ((HIWORD(lParam) & (KF_UP | KF_REPEAT)) == KF_REPEAT) {
        debug(("+"));
	    } else if ((HIWORD(lParam) & KF_UP)
                 && scan == (HIWORD(lParam) & 0xFF)) {
        debug((". U"));
	    } else {
        debug((".\n"));
        if (wParam >= VK_F1 && wParam <= VK_F20)
          debug(("K_F%d", wParam + 1 - VK_F1));
        else
          switch (wParam) {
		      case VK_SHIFT:
            debug(("SHIFT"));
            break;
		      case VK_CONTROL:
            debug(("CTRL"));
            break;
		      case VK_MENU:
            debug(("ALT"));
            break;
		      default:
            debug(("VK_%02x", wParam));
          }
        if (message == WM_SYSKEYDOWN || message == WM_SYSKEYUP)
          debug(("*"));
        debug((", S%02x", scan = (HIWORD(lParam) & 0xFF)));

        ch = MapVirtualKeyEx(wParam, 2, kbd_layout);
        if (ch >= ' ' && ch <= '~')
          debug((", '%c'", ch));
        else if (ch)
          debug((", $%02x", ch));

        if (keys_unicode[0])
          debug((", KB0=%04x", keys_unicode[0]));
        if (keys_unicode[1])
          debug((", KB1=%04x", keys_unicode[1]));
        if (keys_unicode[2])
          debug((", KB2=%04x", keys_unicode[2]));

        if ((keystate[VK_SHIFT] & 0x80) != 0)
          debug((", S"));
        if ((keystate[VK_CONTROL] & 0x80) != 0)
          debug((", C"));
        if ((HIWORD(lParam) & KF_EXTENDED))
          debug((", E"));
        if ((HIWORD(lParam) & KF_UP))
          debug((", U"));
	    }

	    if ((HIWORD(lParam) & (KF_UP | KF_REPEAT)) == KF_REPEAT);
	    else if ((HIWORD(lParam) & KF_UP))
        oldstate[wParam & 0xFF] ^= 0x80;
	    else
        oldstate[wParam & 0xFF] ^= 0x81;

	    for (ch = 0; ch < 256; ch++)
        if (oldstate[ch] != keystate[ch])
          debug((", M%02x=%02x", ch, keystate[ch]));

	    memcpy(oldstate, keystate, sizeof(oldstate));
    }
#endif

    {
      int mod = (keystate[VK_SHIFT] >> 7) |
        (keystate[VK_CONTROL] >> 6) | (keystate[VK_MENU] >> 5);
      int length = pvkey_length[wParam][mod];
      if (length) {
        strcpy((char *) output, pvkey_codes[wParam][mod]);
        return length;
      }
    }

    if (wParam == VK_MENU && (HIWORD(lParam) & KF_EXTENDED)) {
	    keystate[VK_RMENU] = keystate[VK_MENU];
    }


    /* Nastyness with NUMLock - Shift-NUMLock is left alone though */
    if ((funky_type == FUNKY_VT400 ||
         (funky_type <= FUNKY_LINUX && term->app_keypad_keys &&
          !no_applic_k))
        && wParam == VK_NUMLOCK && !(keystate[VK_SHIFT] & 0x80)) {

	    wParam = VK_EXECUTE;

	    /* UnToggle NUMLock */
	    if ((HIWORD(lParam) & (KF_UP | KF_REPEAT)) == 0)
        keystate[VK_NUMLOCK] ^= 1;
    }

    /* And write back the 'adjusted' state */
    SetKeyboardState(keystate);
  }

  /* Disable Auto repeat if required */
  if (term->repeat_off &&
      (HIWORD(lParam) & (KF_UP | KF_REPEAT)) == KF_REPEAT)
    return 0;

  if ((HIWORD(lParam) & KF_ALTDOWN) && (rightaltkey || (keystate[VK_RMENU] & 0x80) == 0))
    left_alt = 1;

  key_down = ((HIWORD(lParam) & KF_UP) == 0);

  /* Make sure Ctrl-ALT is not the same as AltGr for ToAscii unless told. */
  if (left_alt && (keystate[VK_CONTROL] & 0x80)) {
    if (ctrlaltkeys)
	    keystate[VK_MENU] = 0;
    else {
	    keystate[VK_RMENU] = 0x80;
	    left_alt = 0;
    }
  }

  scan = (HIWORD(lParam) & (KF_UP | KF_EXTENDED | 0xFF));
  shift_state = ((keystate[VK_SHIFT] & 0x80) != 0)
    + ((keystate[VK_CONTROL] & 0x80) != 0) * 2;

  /* Note if AltGr was pressed and if it was used as a compose key */
  if (!compose_state) {
    compose_keycode = 0x100;
    if (conf_get_int(conf, CONF_compose_key)) {
	    if (wParam == VK_MENU && (HIWORD(lParam) & KF_EXTENDED))
        compose_keycode = wParam;
    }
    if (wParam == VK_APPS)
	    compose_keycode = wParam;
  }

  if (wParam == compose_keycode) {
    if (compose_state == 0
        && (HIWORD(lParam) & (KF_UP | KF_REPEAT)) == 0) compose_state =
                                                          1;
    else if (compose_state == 1 && (HIWORD(lParam) & KF_UP))
	    compose_state = 2;
    else
	    compose_state = 0;
  } else if (compose_state == 1 && wParam != VK_CONTROL)
    compose_state = 0;

  if (compose_state > 1 && left_alt)
    compose_state = 0;

  /* Sanitize the number pad if not using a PC NumPad */
  if (left_alt || (term->app_keypad_keys && !no_applic_k
                   && funky_type != FUNKY_XTERM)
      || funky_type == FUNKY_VT400 || nethack_keypad || compose_state) {
    if ((HIWORD(lParam) & KF_EXTENDED) == 0) {
	    int nParam = 0;
	    switch (wParam) {
      case VK_INSERT:
        nParam = VK_NUMPAD0;
        break;
      case VK_END:
        nParam = VK_NUMPAD1;
        break;
      case VK_DOWN:
        nParam = VK_NUMPAD2;
        break;
      case VK_NEXT:
        nParam = VK_NUMPAD3;
        break;
      case VK_LEFT:
        nParam = VK_NUMPAD4;
        break;
      case VK_CLEAR:
        nParam = VK_NUMPAD5;
        break;
      case VK_RIGHT:
        nParam = VK_NUMPAD6;
        break;
      case VK_HOME:
        nParam = VK_NUMPAD7;
        break;
      case VK_UP:
        nParam = VK_NUMPAD8;
        break;
      case VK_PRIOR:
        nParam = VK_NUMPAD9;
        break;
      case VK_DELETE:
        nParam = VK_DECIMAL;
        break;
	    }
	    if (nParam) {
        if (keystate[VK_NUMLOCK] & 1)
          shift_state |= 1;
        wParam = nParam;
	    }
    }
  }

  /* If a key is pressed and AltGr is not active */
  if (key_down && (rightaltkey || (keystate[VK_RMENU] & 0x80) == 0) && !compose_state) {
    /* Okay, prepare for most alts then ... */
    if (left_alt)
	    *p++ = '\033';

    /* Lets see if it's a pattern we know all about ... */
    if (wParam == VK_PRIOR && shift_state == 1) {
	    SendMessage(hwnd, WM_VSCROLL, SB_PAGEUP, 0);
	    return 0;
    }
    if (wParam == VK_PRIOR && shift_state == 2) {
	    SendMessage(hwnd, WM_VSCROLL, SB_LINEUP, 0);
	    return 0;
    }
    if (wParam == VK_NEXT && shift_state == 1) {
	    SendMessage(hwnd, WM_VSCROLL, SB_PAGEDOWN, 0);
	    return 0;
    }
    if (wParam == VK_NEXT && shift_state == 2) {
	    SendMessage(hwnd, WM_VSCROLL, SB_LINEDOWN, 0);
	    return 0;
    }
    if ((wParam == VK_PRIOR || wParam == VK_NEXT) && shift_state == 3) {
	    term_scroll_to_selection(term, (wParam == VK_PRIOR ? 0 : 1));
	    return 0;
    }
    if (wParam == VK_INSERT && shift_state == 1) {
	    request_paste(NULL);
	    return 0;
    }
    if (left_alt && wParam == VK_F4 && conf_get_int(conf, CONF_alt_f4)) {
	    return -1;
    }
    if (left_alt && wParam == VK_SPACE && conf_get_int(conf,
                                                       CONF_alt_space)) {
	    SendMessage(hwnd, WM_SYSCOMMAND, SC_KEYMENU, 0);
	    return -1;
    }
    if (left_alt && wParam == VK_RETURN &&
        conf_get_int(conf, CONF_fullscreenonaltenter) &&
        (conf_get_int(conf, CONF_resize_action) != RESIZE_DISABLED)) {
 	    if ((HIWORD(lParam) & (KF_UP | KF_REPEAT)) != KF_REPEAT)
        flip_full_screen();
	    return -1;
    }
    /* Control-Numlock for app-keypad mode switch */
    if (wParam == VK_PAUSE && shift_state == 2) {
	    term->app_keypad_keys ^= 1;
	    return 0;
    }

    /* Nethack keypad */
    if (nethack_keypad && !left_alt) {
	    switch (wParam) {
      case VK_NUMPAD1:
        *p++ = "bB\002\002"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD2:
        *p++ = "jJ\012\012"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD3:
        *p++ = "nN\016\016"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD4:
        *p++ = "hH\010\010"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD5:
        *p++ = shift_state ? '.' : '.';
        return int (p - output);
      case VK_NUMPAD6:
        *p++ = "lL\014\014"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD7:
        *p++ = "yY\031\031"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD8:
        *p++ = "kK\013\013"[shift_state & 3];
        return int (p - output);
      case VK_NUMPAD9:
        *p++ = "uU\025\025"[shift_state & 3];
        return int (p - output);
	    }
    }

    /* Application Keypad */
    if (!left_alt) {
	    int xkey = 0;

	    if (funky_type == FUNKY_VT400 ||
          (funky_type <= FUNKY_LINUX &&
           term->app_keypad_keys && !no_applic_k)) switch (wParam) {
        case VK_EXECUTE:
          xkey = 'P';
          break;
        case VK_DIVIDE:
          xkey = 'Q';
          break;
        case VK_MULTIPLY:
          xkey = 'R';
          break;
        case VK_SUBTRACT:
          xkey = 'S';
          break;
        }
	    if (term->app_keypad_keys && !no_applic_k)
        switch (wParam) {
        case VK_NUMPAD0:
          xkey = 'p';
          break;
        case VK_NUMPAD1:
          xkey = 'q';
          break;
        case VK_NUMPAD2:
          xkey = 'r';
          break;
        case VK_NUMPAD3:
          xkey = 's';
          break;
        case VK_NUMPAD4:
          xkey = 't';
          break;
        case VK_NUMPAD5:
          xkey = 'u';
          break;
        case VK_NUMPAD6:
          xkey = 'v';
          break;
        case VK_NUMPAD7:
          xkey = 'w';
          break;
        case VK_NUMPAD8:
          xkey = 'x';
          break;
        case VK_NUMPAD9:
          xkey = 'y';
          break;

        case VK_DECIMAL:
          xkey = 'n';
          break;
        case VK_ADD:
          if (funky_type == FUNKY_XTERM) {
            if (shift_state)
              xkey = 'l';
            else
              xkey = 'k';
          } else if (shift_state)
            xkey = 'm';
          else
            xkey = 'l';
          break;

        case VK_DIVIDE:
          if (funky_type == FUNKY_XTERM)
            xkey = 'o';
          break;
        case VK_MULTIPLY:
          if (funky_type == FUNKY_XTERM)
            xkey = 'j';
          break;
        case VK_SUBTRACT:
          if (funky_type == FUNKY_XTERM)
            xkey = 'm';
          break;

        case VK_RETURN:
          if (HIWORD(lParam) & KF_EXTENDED)
            xkey = 'M';
          break;
        }
	    if (xkey) {
        if (term->vt52_mode) {
          if (xkey >= 'P' && xkey <= 'S')
            p += sprintf((char *) p, "\x1B%c", xkey);
          else
            p += sprintf((char *) p, "\x1B?%c", xkey);
        } else
          p += sprintf((char *) p, "\x1BO%c", xkey);
        return int (p - output);
	    }
    }

    if (wParam == VK_BACK && shift_state == 0) {	/* Backspace */
	    *p++ = (conf_get_int(conf, CONF_bksp_is_delete) ? 0x7F : 0x08);
	    *p++ = 0;
	    return -2;
    }
    if (wParam == VK_BACK && shift_state == 1) {	/* Shift Backspace */
	    /* We do the opposite of what is configured */
	    *p++ = (conf_get_int(conf, CONF_bksp_is_delete) ? 0x08 : 0x7F);
	    *p++ = 0;
	    return -2;
    }
    if (wParam == VK_TAB && shift_state == 1) {	/* Shift tab */
	    *p++ = 0x1B;
	    *p++ = '[';
	    *p++ = 'Z';
	    return int (p - output);
    }
    if (wParam == VK_SPACE && shift_state == 2) {	/* Ctrl-Space */
	    *p++ = 0;
	    return int (p - output);
    }
    if (wParam == VK_SPACE && shift_state == 3) {	/* Ctrl-Shift-Space */
	    *p++ = 160;
	    return int (p - output);
    }
    if (wParam == VK_CANCEL && shift_state == 2) {	/* Ctrl-Break */
	    if (back)
        back->special(backhandle, TS_BRK);
	    return 0;
    }
    if (wParam == VK_PAUSE) {      /* Break/Pause */
	    *p++ = 26;
	    *p++ = 0;
	    return -2;
    }
    /* Control-2 to Control-8 are special */
    if (shift_state == 2 && wParam >= '2' && wParam <= '8') {
	    *p++ = "\000\033\034\035\036\037\177"[wParam - '2'];
	    return int (p - output);
    }
    if (shift_state == 2 && (wParam == 0xBD || wParam == 0xBF)) {
	    *p++ = 0x1F;
	    return int (p - output);
    }
    if (shift_state == 2 && (wParam == 0xDF || wParam == 0xDC)) {
	    *p++ = 0x1C;
	    return int (p - output);
    }
    if (shift_state == 3 && wParam == 0xDE) {
	    *p++ = 0x1E;	       /* Ctrl-~ == Ctrl-^ in xterm at least */
	    return int (p - output);
    }
    if (shift_state == 0 && wParam == VK_RETURN && term->cr_lf_return) {
	    *p++ = '\r';
	    *p++ = '\n';
	    return int (p - output);
    }

    /*
     * Next, all the keys that do tilde codes. (ESC '[' nn '~',
     * for integer decimal nn.)
     *
     * We also deal with the weird ones here. Linux VCs replace F1
     * to F5 by ESC [ [ A to ESC [ [ E. rxvt doesn't do _that_, but
     * does replace Home and End (1~ and 4~) by ESC [ H and ESC O w
     * respectively.
     */
    code = 0;
    switch (wParam) {
	  case VK_F1:
	    code = (keystate[VK_SHIFT] & 0x80 ? 23 : 11);
	    break;
	  case VK_F2:
	    code = (keystate[VK_SHIFT] & 0x80 ? 24 : 12);
	    break;
	  case VK_F3:
	    code = (keystate[VK_SHIFT] & 0x80 ? 25 : 13);
	    break;
	  case VK_F4:
	    code = (keystate[VK_SHIFT] & 0x80 ? 26 : 14);
	    break;
	  case VK_F5:
	    code = (keystate[VK_SHIFT] & 0x80 ? 28 : 15);
	    break;
	  case VK_F6:
	    code = (keystate[VK_SHIFT] & 0x80 ? 29 : 17);
	    break;
	  case VK_F7:
	    code = (keystate[VK_SHIFT] & 0x80 ? 31 : 18);
	    break;
	  case VK_F8:
	    code = (keystate[VK_SHIFT] & 0x80 ? 32 : 19);
	    break;
	  case VK_F9:
	    code = (keystate[VK_SHIFT] & 0x80 ? 33 : 20);
	    break;
	  case VK_F10:
	    code = (keystate[VK_SHIFT] & 0x80 ? 34 : 21);
	    break;
	  case VK_F11:
	    code = 23;
	    break;
	  case VK_F12:
	    code = 24;
	    break;
	  case VK_F13:
	    code = 25;
	    break;
	  case VK_F14:
	    code = 26;
	    break;
	  case VK_F15:
	    code = 28;
	    break;
	  case VK_F16:
	    code = 29;
	    break;
	  case VK_F17:
	    code = 31;
	    break;
	  case VK_F18:
	    code = 32;
	    break;
	  case VK_F19:
	    code = 33;
	    break;
	  case VK_F20:
	    code = 34;
	    break;
    }
    if ((shift_state&2) == 0) switch (wParam) {
      case VK_HOME:
        code = 1;
        break;
      case VK_INSERT:
        code = 2;
        break;
      case VK_DELETE:
        code = 3;
        break;
      case VK_END:
        code = 4;
        break;
      case VK_PRIOR:
        code = 5;
        break;
      case VK_NEXT:
        code = 6;
        break;
      }
    /* Reorder edit keys to physical order */
    if (funky_type == FUNKY_VT400 && code <= 6)
	    code = "\0\2\1\4\5\3\6"[code];

    if (term->vt52_mode && code > 0 && code <= 6) {
	    p += sprintf((char *) p, "\x1B%c", " HLMEIG"[code]);
	    return int (p - output);
    }

    if (funky_type == FUNKY_SCO && code >= 11 && code <= 34) {
	    /* SCO function keys */
	    char codes[] = "MNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz@[\\]^_`{";
	    int index = 0;
	    switch (wParam) {
      case VK_F1: index = 0; break;
      case VK_F2: index = 1; break;
      case VK_F3: index = 2; break;
      case VK_F4: index = 3; break;
      case VK_F5: index = 4; break;
      case VK_F6: index = 5; break;
      case VK_F7: index = 6; break;
      case VK_F8: index = 7; break;
      case VK_F9: index = 8; break;
      case VK_F10: index = 9; break;
      case VK_F11: index = 10; break;
      case VK_F12: index = 11; break;
	    }
	    if (keystate[VK_SHIFT] & 0x80) index += 12;
	    if (keystate[VK_CONTROL] & 0x80) index += 24;
	    p += sprintf((char *) p, "\x1B[%c", codes[index]);
	    return int (p - output);
    }
    if (funky_type == FUNKY_SCO &&     /* SCO small keypad */
        code >= 1 && code <= 6) {
	    char codes[] = "HL.FIG";
	    if (code == 3) {
        *p++ = '\x7F';
	    } else {
        p += sprintf((char *) p, "\x1B[%c", codes[code-1]);
	    }
	    return int (p - output);
    }
    if ((term->vt52_mode || funky_type == FUNKY_VT100P) && code >= 11 && code <= 24) {
	    int offt = 0;
	    if (code > 15)
        offt++;
	    if (code > 21)
        offt++;
	    if (term->vt52_mode)
        p += sprintf((char *) p, "\x1B%c", code + 'P' - 11 - offt);
	    else
        p +=
          sprintf((char *) p, "\x1BO%c", code + 'P' - 11 - offt);
	    return int (p - output);
    }
    if (funky_type == FUNKY_LINUX && code >= 11 && code <= 15) {
	    p += sprintf((char *) p, "\x1B[[%c", code + 'A' - 11);
	    return int (p - output);
    }
    if (funky_type == FUNKY_XTERM && code >= 11 && code <= 14) {
	    if (term->vt52_mode)
        p += sprintf((char *) p, "\x1B%c", code + 'P' - 11);
	    else
        p += sprintf((char *) p, "\x1BO%c", code + 'P' - 11);
	    return int (p - output);
    }
    if ((code == 1 || code == 4) &&
        conf_get_int(conf, CONF_rxvt_homeend)) {
	    p += sprintf((char *) p, code == 1 ? "\x1B[H" : "\x1BOw");
	    return int (p - output);
    }
    if (code) {
	    p += sprintf((char *) p, "\x1B[%d~", code);
	    return int (p - output);
    }

    /*
     * Now the remaining keys (arrows and Keypad 5. Keypad 5 for
     * some reason seems to send VK_CLEAR to Windows...).
     */
    {
	    char xkey = 0;
	    switch (wParam) {
      case VK_UP:
        xkey = 'A';
        break;
      case VK_DOWN:
        xkey = 'B';
        break;
      case VK_RIGHT:
        xkey = 'C';
        break;
      case VK_LEFT:
        xkey = 'D';
        break;
      case VK_CLEAR:
        xkey = 'G';
        break;
	    }
	    if (xkey) {
        p += format_arrow_key((char *)p, term, xkey, shift_state);
        return int (p - output);
	    }
    }

    /*
     * Finally, deal with Return ourselves. (Win95 seems to
     * foul it up when Alt is pressed, for some reason.)
     */
    if (wParam == VK_RETURN) {     /* Return */
	    *p++ = 0x0D;
	    *p++ = 0;
	    return -2;
    }

    if (left_alt && wParam >= VK_NUMPAD0 && wParam <= VK_NUMPAD9)
	    alt_sum = alt_sum * 10 + (int) wParam - VK_NUMPAD0;
    else
	    alt_sum = 0;
  }

  /* Okay we've done everything interesting; let windows deal with 
   * the boring stuff */
  {
    BOOL capsOn=0;

    /* helg: clear CAPS LOCK state if caps lock switches to cyrillic */
    if(keystate[VK_CAPITAL] != 0 &&
       conf_get_int(conf, CONF_xlat_capslockcyr)) {
	    capsOn= !left_alt;
	    keystate[VK_CAPITAL] = 0;
    }

    /* XXX how do we know what the max size of the keys array should
     * be is? There's indication on MS' website of an Inquire/InquireEx
     * functioning returning a KBINFO structure which tells us. */
    if (osVersion.dwPlatformId == VER_PLATFORM_WIN32_NT && p_ToUnicodeEx) {
      r = p_ToUnicodeEx(wParam, scan, keystate, keys_unicode,
                        lenof(keys_unicode), 0, kbd_layout);
    } else {
	    /* XXX 'keys' parameter is declared in MSDN documentation as
	     * 'LPWORD lpChar'.
	     * The experience of a French user indicates that on
	     * Win98, WORD[] should be passed in, but on Win2K, it should
	     * be BYTE[]. German WinXP and my Win2K with "US International"
	     * driver corroborate this.
	     * Experimentally I've conditionalised the behaviour on the
	     * Win9x/NT split, but I suspect it's worse than that.
	     * See wishlist item `win-dead-keys' for more horrible detail
	     * and speculations. */
	    int i;
	    static WORD keys[3];
	    static BYTE keysb[3];
	    r = ToAsciiEx((UINT) wParam, scan, keystate, keys, 0, kbd_layout);
	    if (r > 0) {
        for (i = 0; i < r; i++) {
          keysb[i] = (BYTE)keys[i];
        }
        MultiByteToWideChar(CP_ACP, 0, (LPCSTR)keysb, r,
                            keys_unicode, lenof(keys_unicode));
	    }
    }
#ifdef SHOW_TOASCII_RESULT
    if (r == 1 && !key_down) {
	    if (alt_sum) {
        if (in_utf(term) || ucsdata.dbcs_screenfont)
          debug((", (U+%04x)", alt_sum));
        else
          debug((", LCH(%d)", alt_sum));
	    } else {
        debug((", ACH(%d)", keys_unicode[0]));
	    }
    } else if (r > 0) {
	    int r1;
	    debug((", ASC("));
	    for (r1 = 0; r1 < r; r1++) {
        debug(("%s%d", r1 ? "," : "", keys_unicode[r1]));
	    }
	    debug((")"));
    }
#endif
    if (r > 0) {
	    WCHAR keybuf;

	    p = output;
	    for (i = 0; i < r; i++) {
        wchar_t wch = keys_unicode[i];

        if (compose_state == 2 && wch >= ' ' && wch < 0x80) {
          compose_char = wch;
          compose_state++;
          continue;
        }
        if (compose_state == 3 && wch >= ' ' && wch < 0x80) {
          int nc;
          compose_state = 0;

          if ((nc = check_compose(compose_char, wch)) == -1) {
            MessageBeep(MB_ICONHAND);
            return 0;
          }
          keybuf = nc;
          term_seen_key_event(term);
          if (ldisc)
            luni_send(ldisc, &keybuf, 1, 1);
          continue;
        }

        compose_state = 0;

        if (!key_down) {
          if (alt_sum) {
            if (in_utf(term) || ucsdata.dbcs_screenfont) {
              keybuf = alt_sum;
              term_seen_key_event(term);
              if (ldisc)
                luni_send(ldisc, &keybuf, 1, 1);
            } else {
              char ch = (char) alt_sum;
              /*
               * We need not bother about stdin
               * backlogs here, because in GUI PuTTY
               * we can't do anything about it
               * anyway; there's no means of asking
               * Windows to hold off on KEYDOWN
               * messages. We _have_ to buffer
               * everything we're sent.
               */
              term_seen_key_event(term);
              if (ldisc)
                ldisc_send(ldisc, (char *) &ch, 1, 1);
            }
            alt_sum = 0;
          } else {
            term_seen_key_event(term);
            if (ldisc)
              luni_send(ldisc, &wch, 1, 1);
          }
        } else {
          if(capsOn && wch < 0x80) {
            WCHAR cbuf[2];
            cbuf[0] = 27;
            cbuf[1] = xlat_uskbd2cyrllic(wch);
            term_seen_key_event(term);
            if (ldisc)
              luni_send(ldisc, cbuf+!left_alt, 1+!!left_alt, 1);
          } else if (alt_metabit) {
            if (left_alt) {
              char cbuf = (char) (wch | (1 << 7));
              ldisc_send(ldisc, &cbuf, 1, 1);
            } else {
              lpage_send(ldisc, kbd_codepage, (char *) &wch, 1, 1);
            }
          } else {
            WCHAR cbuf[2];
            cbuf[0] = '\033';
            cbuf[1] = wch;
            term_seen_key_event(term);
            if (ldisc)
              luni_send(ldisc, cbuf +!left_alt, 1+!!left_alt, 1);
          }
        }
        show_mouseptr(0);
	    }

	    /* This is so the ALT-Numpad and dead keys work correctly. */
	    keys_unicode[0] = 0;

	    return int (p - output);
    }
    /* If we're definitly not building up an ALT-54321 then clear it */
    if (!left_alt)
	    keys_unicode[0] = 0;
    /* If we will be using alt_sum fix the 256s */
    else if (keys_unicode[0] && (in_utf(term) || ucsdata.dbcs_screenfont))
	    keys_unicode[0] = 10;
  }

  /*
   * ALT alone may or may not want to bring up the System menu.
   * If it's not meant to, we return 0 on presses or releases of
   * ALT, to show that we've swallowed the keystroke. Otherwise
   * we return -1, which means Windows will give the keystroke
   * its default handling (i.e. bring up the System menu).
   */
  if (wParam == VK_MENU && !conf_get_int(conf, CONF_alt_only))
    return 0;

  return -1;
}

void set_title(void *frontend, char *title)
{
  sfree(window_name);
  window_name = snewn(1 + strlen(title), char);
  strcpy(window_name, title);
  if (conf_get_int(conf, CONF_win_name_always) || !IsIconic(hwnd))
    SetWindowText(hwnd, title);
}

void set_icon(void *frontend, char *title)
{
  sfree(icon_name);
  icon_name = snewn(1 + strlen(title), char);
  strcpy(icon_name, title);
  if (!conf_get_int(conf, CONF_win_name_always) && IsIconic(hwnd))
    SetWindowText(hwnd, title);
}

void set_sbar(void *frontend, int total, int start, int page)
{
  SCROLLINFO si;

  if (!conf_get_int(conf, is_full_screen()?
                    CONF_scrollbar_in_fullscreen : CONF_scrollbar))
    return;

  si.cbSize = sizeof(si);
  si.fMask = SIF_ALL | SIF_DISABLENOSCROLL;
  si.nMin = 0;
  si.nMax = total - 1;
  si.nPage = page;
  si.nPos = start;
  if (hwnd)
    SetScrollInfo(hwnd, SB_VERT, &si, TRUE);
}

Context get_ctx(void *frontend)
{
  HDC hdc;
  if (hwnd) {
    hdc = GetDC(hwnd);
    if (hdc && pal)
      SelectPalette(hdc, pal, FALSE);
    return hdc;
  } else
    return NULL;
}

void free_ctx(Context ctx)
{
  SelectPalette(ctx, (HPALETTE) GetStockObject(DEFAULT_PALETTE), FALSE);
  ReleaseDC(hwnd, ctx);
}

static void real_palette_set(int n, int r, int g, int b)
{
  if (pal) {
    logpal->palPalEntry[n].peRed = r;
    logpal->palPalEntry[n].peGreen = g;
    logpal->palPalEntry[n].peBlue = b;
    logpal->palPalEntry[n].peFlags = PC_NOCOLLAPSE;
    colours[n] = PALETTERGB(r, g, b);
    SetPaletteEntries(pal, 0, NALLCOLOURS, logpal->palPalEntry);
  } else
    colours[n] = D2D_RGB(r, g, b);
}

void palette_set(void *frontend, int n, int r, int g, int b)
{
  if (n >= 16)
    n += 256 - 16;
  if (n >= NALLCOLOURS)
    return;
  real_palette_set(n, r, g, b);
  if (pal) {
    HDC hdc = get_ctx(frontend);
    UnrealizeObject(pal);
    RealizePalette(hdc);
    free_ctx(hdc);
  } else {
    if (n == (ATTR_DEFBG >> ATTR_BGSHIFT))
      /* If Default Background changes, we need to ensure any
       * space between the text area and the window border is
       * redrawn. */
      InvalidateRect(hwnd, NULL, TRUE);
  }
}

void palette_reset(void *frontend)
{
  int i;

  /* And this */
  for (i = 0; i < NALLCOLOURS; i++) {
    if (pal) {
      logpal->palPalEntry[i].peRed = defpal[i].rgbtRed;
      logpal->palPalEntry[i].peGreen = defpal[i].rgbtGreen;
      logpal->palPalEntry[i].peBlue = defpal[i].rgbtBlue;
      logpal->palPalEntry[i].peFlags = 0;
      colours[i] = PALETTERGB(defpal[i].rgbtRed,
                              defpal[i].rgbtGreen, defpal[i].rgbtBlue);
    } else
      colours[i] = D2D_RGB(defpal[i].rgbtRed,
                           defpal[i].rgbtGreen, defpal[i].rgbtBlue);
  }

  if (pal) {
    HDC hdc;
    SetPaletteEntries(pal, 0, NALLCOLOURS, logpal->palPalEntry);
    hdc = get_ctx(frontend);
    RealizePalette(hdc);
    free_ctx(hdc);
  } else {
    /* Default Background may have changed. Ensure any space between
     * text area and window border is redrawn. */
    InvalidateRect(hwnd, NULL, TRUE);
  }
}

void write_aclip(void *frontend, char *data, int len, int must_deselect)
{
  HGLOBAL clipdata;
  void *lock;

  clipdata = GlobalAlloc(GMEM_DDESHARE | GMEM_MOVEABLE, len + 1);
  if (!clipdata)
    return;
  lock = GlobalLock(clipdata);
  if (!lock)
    return;
  memcpy(lock, data, len);
  ((unsigned char *) lock)[len] = 0;
  GlobalUnlock(clipdata);

  if (!must_deselect)
    SendMessage(hwnd, WM_IGNORE_CLIP, TRUE, 0);

  if (OpenClipboard(hwnd)) {
    EmptyClipboard();
    SetClipboardData(CF_TEXT, clipdata);
    CloseClipboard();
  } else
    GlobalFree(clipdata);

  if (!must_deselect)
    SendMessage(hwnd, WM_IGNORE_CLIP, FALSE, 0);
}

/*
 * Note: unlike write_aclip() this will not append a nul.
 */
void write_clip(void *frontend, wchar_t * data, int *attr, int len,
                int must_deselect)
{
  HGLOBAL clipdata, clipdata2, clipdata3;
  int len2;
  void *lock, *lock2, *lock3;

  len2 = WideCharToMultiByte(CP_ACP, 0, data, len, 0, 0, NULL, NULL);

  clipdata = GlobalAlloc(GMEM_DDESHARE | GMEM_MOVEABLE, len * sizeof(wchar_t));
  clipdata2 = GlobalAlloc(GMEM_DDESHARE | GMEM_MOVEABLE, len2);

  if (!clipdata || !clipdata2) {
    if (clipdata)
      GlobalFree(clipdata);
    if (clipdata2)
      GlobalFree(clipdata2);
    return;
  }
  if (!(lock = GlobalLock(clipdata))) {
    GlobalFree(clipdata);
    GlobalFree(clipdata2);
    return;
  }
  if (!(lock2 = GlobalLock(clipdata2))) {
    GlobalUnlock(clipdata);
    GlobalFree(clipdata);
    GlobalFree(clipdata2);
    return;
  }

  memcpy(lock, data, len * sizeof(wchar_t));
  WideCharToMultiByte(CP_ACP, 0, data, len, (LPSTR) lock2, len2, NULL, NULL);

  if (conf_get_int(conf, CONF_rtf_paste)) {
    wchar_t unitab[256];
    char *rtf = NULL;
    unsigned char *tdata = (unsigned char *) lock2;
    wchar_t *udata = (wchar_t *) lock;
    int rtflen = 0, uindex = 0, tindex = 0;
    int rtfsize = 0;
    int multilen, blen, alen, totallen, i;
    char before[16], after[4];
    int fgcolour, lastfgcolour = 0;
    int bgcolour, lastbgcolour = 0;
    int attrBold, lastAttrBold = 0;
    int attrUnder, lastAttrUnder = 0;
    int palette[NALLCOLOURS];
    int numcolours;
    FontSpec *font = conf_get_fontspec(conf, CONF_font);

    get_unitab(CP_ACP, unitab, 0);

    rtfsize = 100 + (int) strlen(font->name);
    rtf = snewn(rtfsize, char);
    rtflen =
      sprintf(rtf,
              "{\\rtf1\\ansi\\deff0{\\fonttbl\\f0\\fmodern %s;}\\f0\\fs%d",
              font->name, font->height * 2);

    /*
     * Add colour palette
     * {\colortbl ;\red255\green0\blue0;\red0\green0\blue128;}
     */

    /*
     * First - Determine all colours in use
     *    o  Foregound and background colours share the same palette
     */
    if (attr) {
      memset(palette, 0, sizeof(palette));
      for (i = 0; i < (len - 1); i++) {
        fgcolour = ((attr[i] & ATTR_FGMASK) >> ATTR_FGSHIFT);
        bgcolour = ((attr[i] & ATTR_BGMASK) >> ATTR_BGSHIFT);

        if (attr[i] & ATTR_REVERSE) {
          int tmpcolour = fgcolour;     /* Swap foreground and background */
          fgcolour = bgcolour;
          bgcolour = tmpcolour;
        }

        if (bold_colours && (attr[i] & ATTR_BOLD)) {
          if (fgcolour < 8)     /* ANSI colours */
            fgcolour += 8;
          else if (fgcolour >= 256)     /* Default colours */
            fgcolour++;
        }

        if (attr[i] & ATTR_BLINK) {
          if (bgcolour < 8)     /* ANSI colours */
            bgcolour += 8;
          else if (bgcolour >= 256)     /* Default colours */
            bgcolour++;
        }

        palette[fgcolour]++;
        palette[bgcolour]++;
      }

      /*
       * Next - Create a reduced palette
       */
      numcolours = 0;
      for (i = 0; i < NALLCOLOURS; i++) {
        if (palette[i] != 0)
          palette[i] = ++numcolours;
      }

      /*
       * Finally - Write the colour table
       */
      rtf = sresize(rtf, rtfsize + (numcolours * 25), char);
      strcat(rtf, "{\\colortbl ;");
      rtflen = (int) strlen(rtf);

      for (i = 0; i < NALLCOLOURS; i++) {
        if (palette[i] != 0) {
          rtflen +=
            sprintf(&rtf[rtflen], "\\red%d\\green%d\\blue%d;",
                    defpal[i].rgbtRed, defpal[i].rgbtGreen,
                    defpal[i].rgbtBlue);
        }
      }
      strcpy(&rtf[rtflen], "}");
      rtflen++;
    }

    /*
     * We want to construct a piece of RTF that specifies the
     * same Unicode text. To do this we will read back in
     * parallel from the Unicode data in `udata' and the
     * non-Unicode data in `tdata'. For each character in
     * `tdata' which becomes the right thing in `udata' when
     * looked up in `unitab', we just copy straight over from
     * tdata. For each one that doesn't, we must WCToMB it
     * individually and produce a \u escape sequence.
     * 
     * It would probably be more robust to just bite the bullet
     * and WCToMB each individual Unicode character one by one,
     * then MBToWC each one back to see if it was an accurate
     * translation; but that strikes me as a horrifying number
     * of Windows API calls so I want to see if this faster way
     * will work. If it screws up badly we can always revert to
     * the simple and slow way.
     */
    while (tindex < len2 && uindex < len && tdata[tindex] && udata[uindex]) {
      if (tindex + 1 < len2 &&
          tdata[tindex] == '\r' && tdata[tindex + 1] == '\n') {
        tindex++;
        uindex++;
      }

      /*
       * Set text attributes
       */
      if (attr) {
        if (rtfsize < rtflen + 64) {
          rtfsize = rtflen + 512;
          rtf = sresize(rtf, rtfsize, char);
        }

        /*
         * Determine foreground and background colours
         */
        fgcolour = ((attr[tindex] & ATTR_FGMASK) >> ATTR_FGSHIFT);
        bgcolour = ((attr[tindex] & ATTR_BGMASK) >> ATTR_BGSHIFT);

        if (attr[tindex] & ATTR_REVERSE) {
          int tmpcolour = fgcolour;     /* Swap foreground and background */
          fgcolour = bgcolour;
          bgcolour = tmpcolour;
        }

        if (bold_colours && (attr[tindex] & ATTR_BOLD)) {
          if (fgcolour < 8)     /* ANSI colours */
            fgcolour += 8;
          else if (fgcolour >= 256)     /* Default colours */
            fgcolour++;
        }

        if (attr[tindex] & ATTR_BLINK) {
          if (bgcolour < 8)     /* ANSI colours */
            bgcolour += 8;
          else if (bgcolour >= 256)     /* Default colours */
            bgcolour++;
        }

        /*
         * Collect other attributes
         */
        if (bold_font_mode != BOLD_NONE)
          attrBold = attr[tindex] & ATTR_BOLD;
        else
          attrBold = 0;

        attrUnder = attr[tindex] & ATTR_UNDER;

        /*
         * Reverse video
         *   o  If video isn't reversed, ignore colour attributes for default foregound
         *      or background.
         *   o  Special case where bolded text is displayed using the default foregound
         *      and background colours - force to bolded RTF.
         */
        if (!(attr[tindex] & ATTR_REVERSE)) {
          if (bgcolour >= 256)  /* Default color */
            bgcolour = -1;      /* No coloring */

          if (fgcolour >= 256) {        /* Default colour */
            if (bold_colours && (fgcolour & 1) && bgcolour == -1)
              attrBold = ATTR_BOLD;     /* Emphasize text with bold attribute */

            fgcolour = -1;      /* No coloring */
          }
        }

        /*
         * Write RTF text attributes
         */
        if (lastfgcolour != fgcolour) {
          lastfgcolour = fgcolour;
          rtflen +=
            sprintf(&rtf[rtflen], "\\cf%d ",
                    (fgcolour >= 0) ? palette[fgcolour] : 0);
        }

        if (lastbgcolour != bgcolour) {
          lastbgcolour = bgcolour;
          rtflen +=
            sprintf(&rtf[rtflen], "\\highlight%d ",
                    (bgcolour >= 0) ? palette[bgcolour] : 0);
        }

        if (lastAttrBold != attrBold) {
          lastAttrBold = attrBold;
          rtflen += sprintf(&rtf[rtflen], "%s", attrBold ? "\\b " : "\\b0 ");
        }

        if (lastAttrUnder != attrUnder) {
          lastAttrUnder = attrUnder;
          rtflen +=
            sprintf(&rtf[rtflen], "%s", attrUnder ? "\\ul " : "\\ulnone ");
        }
      }

      if (unitab[tdata[tindex]] == udata[uindex]) {
        multilen = 1;
        before[0] = '\0';
        after[0] = '\0';
        blen = alen = 0;
      } else {
        multilen = WideCharToMultiByte(CP_ACP, 0, unitab + uindex, 1,
                                       NULL, 0, NULL, NULL);
        if (multilen != 1) {
          blen = sprintf(before, "{\\uc%d\\u%d", multilen, udata[uindex]);
          alen = 1;
          strcpy(after, "}");
        } else {
          blen = sprintf(before, "\\u%d", udata[uindex]);
          alen = 0;
          after[0] = '\0';
        }
      }
      assert(tindex + multilen <= len2);
      totallen = blen + alen;
      for (i = 0; i < multilen; i++) {
        if (tdata[tindex + i] == '\\' ||
            tdata[tindex + i] == '{' || tdata[tindex + i] == '}')
          totallen += 2;
        else if (tdata[tindex + i] == 0x0D || tdata[tindex + i] == 0x0A)
          totallen += 6;        /* \par\r\n */
        else if (tdata[tindex + i] > 0x7E || tdata[tindex + i] < 0x20)
          totallen += 4;
        else
          totallen++;
      }

      if (rtfsize < rtflen + totallen + 3) {
        rtfsize = rtflen + totallen + 512;
        rtf = sresize(rtf, rtfsize, char);
      }

      strcpy(rtf + rtflen, before);
      rtflen += blen;
      for (i = 0; i < multilen; i++) {
        if (tdata[tindex + i] == '\\' ||
            tdata[tindex + i] == '{' || tdata[tindex + i] == '}') {
          rtf[rtflen++] = '\\';
          rtf[rtflen++] = tdata[tindex + i];
        } else if (tdata[tindex + i] == 0x0D || tdata[tindex + i] == 0x0A) {
          rtflen += sprintf(rtf + rtflen, "\\par\r\n");
        } else if (tdata[tindex + i] > 0x7E || tdata[tindex + i] < 0x20) {
          rtflen += sprintf(rtf + rtflen, "\\'%02x", tdata[tindex + i]);
        } else {
          rtf[rtflen++] = tdata[tindex + i];
        }
      }
      strcpy(rtf + rtflen, after);
      rtflen += alen;

      tindex += multilen;
      uindex++;
    }

    rtf[rtflen++] = '}';        /* Terminate RTF stream */
    rtf[rtflen++] = '\0';
    rtf[rtflen++] = '\0';

    clipdata3 = GlobalAlloc(GMEM_DDESHARE | GMEM_MOVEABLE, rtflen);
    if (clipdata3 && (lock3 = GlobalLock(clipdata3)) != NULL) {
      memcpy(lock3, rtf, rtflen);
      GlobalUnlock(clipdata3);
    }
    sfree(rtf);
  } else
    clipdata3 = NULL;

  GlobalUnlock(clipdata);
  GlobalUnlock(clipdata2);

  if (!must_deselect)
    SendMessage(hwnd, WM_IGNORE_CLIP, TRUE, 0);

  if (OpenClipboard(hwnd)) {
    EmptyClipboard();
    SetClipboardData(CF_UNICODETEXT, clipdata);
    SetClipboardData(CF_TEXT, clipdata2);
    if (clipdata3)
      SetClipboardData(RegisterClipboardFormat(CF_RTF), clipdata3);
    CloseClipboard();
  } else {
    GlobalFree(clipdata);
    GlobalFree(clipdata2);
  }

  if (!must_deselect)
    SendMessage(hwnd, WM_IGNORE_CLIP, FALSE, 0);
}

static DWORD WINAPI clipboard_read_threadfunc(void *param)
{
  HWND hwnd = (HWND) param;
  HGLOBAL clipdata;

  if (OpenClipboard(NULL)) {
    if ((clipdata = GetClipboardData(CF_UNICODETEXT))) {
      SendMessage(hwnd, WM_GOT_CLIPDATA, (WPARAM) 1, (LPARAM) clipdata);
    } else if ((clipdata = GetClipboardData(CF_TEXT))) {
      SendMessage(hwnd, WM_GOT_CLIPDATA, (WPARAM) 0, (LPARAM) clipdata);
    }
    CloseClipboard();
  }

  return 0;
}

static int process_clipdata(HGLOBAL clipdata, int unicode)
{
  sfree(clipboard_contents);
  clipboard_contents = NULL;
  clipboard_length = 0;

  if (unicode) {
    wchar_t *p = (wchar_t *) GlobalLock(clipdata);
    wchar_t *p2;

    if (p) {
      /* Unwilling to rely on Windows having wcslen() */
      for (p2 = p; *p2; p2++);
      clipboard_length = p2 - p;
      clipboard_contents = snewn(clipboard_length + 1, wchar_t);
      memcpy(clipboard_contents, p, clipboard_length * sizeof(wchar_t));
      clipboard_contents[clipboard_length] = L'\0';
      return TRUE;
    }
  } else {
    char *s = (char *) GlobalLock(clipdata);
    int i;

    if (s) {
      i = MultiByteToWideChar(CP_ACP, 0, s, (int) strlen(s) + 1, 0, 0);
      clipboard_contents = snewn(i, wchar_t);
      MultiByteToWideChar(CP_ACP, 0, s, (int) strlen(s) + 1,
                          clipboard_contents, i);
      clipboard_length = i - 1;
      clipboard_contents[clipboard_length] = L'\0';
      return TRUE;
    }
  }

  return FALSE;
}

void request_paste(void *frontend)
{
  /*
   * I always thought pasting was synchronous in Windows; the
   * clipboard access functions certainly _look_ synchronous,
   * unlike the X ones. But in fact it seems that in some
   * situations the contents of the clipboard might not be
   * immediately available, and the clipboard-reading functions
   * may block. This leads to trouble if the application
   * delivering the clipboard data has to get hold of it by -
   * for example - talking over a network connection which is
   * forwarded through this very PuTTY.
   *
   * Hence, we spawn a subthread to read the clipboard, and do
   * our paste when it's finished. The thread will send a
   * message back to our main window when it terminates, and
   * that tells us it's OK to paste.
   */
  DWORD in_threadid;    /* required for Win9x */
  CreateThread(NULL, 0, clipboard_read_threadfunc, hwnd, 0, &in_threadid);
}

void get_clip(void *frontend, wchar_t ** p, int *len)
{
  if (p) {
    *p = clipboard_contents;
    *len = (int) clipboard_length;
  }
}

#if 0
/*
 * Move `lines' lines from position `from' to position `to' in the
 * window.
 */
void optimised_move(void *frontend, int to, int from, int lines)
{
  RECT r;
  int min, max;

  min = (to < from ? to : from);
  max = to + from - min;

  r.left = offset_width;
  r.right = offset_width + term->cols * box_width;
  r.top = offset_height + min * box_height;
  r.bottom = offset_height + (max + lines) * box_height;
  ScrollWindow(hwnd, 0, (to - from) * box_height, &r, &r);
}
#endif

/*
 * Print a message box and perform a fatal exit.
 */
void fatalbox(const char *fmt, ...)
{
  va_list ap;
  char *stuff, morestuff[100];

  va_start(ap, fmt);
  stuff = dupvprintf(fmt, ap);
  va_end(ap);
  sprintf(morestuff, "%.70s Fatal Error", appname);
  MessageBox(hwnd, stuff, morestuff, MB_ICONERROR | MB_OK);
  sfree(stuff);
  cleanup_exit(1);
}

/*
 * Print a modal (Really Bad) message box and perform a fatal exit.
 */
void modalfatalbox(const char *fmt, ...)
{
  va_list ap;
  char *stuff, morestuff[100];

  va_start(ap, fmt);
  stuff = dupvprintf(fmt, ap);
  va_end(ap);
  sprintf(morestuff, "%.70s Fatal Error", appname);
  MessageBox(hwnd, stuff, morestuff, MB_SYSTEMMODAL | MB_ICONERROR | MB_OK);
  sfree(stuff);
  cleanup_exit(1);
}

/*
 * Print a message box and don't close the connection.
 */
void nonfatal(const char *fmt, ...)
{
  va_list ap;
  char *stuff, morestuff[100];

  va_start(ap, fmt);
  stuff = dupvprintf(fmt, ap);
  va_end(ap);
  sprintf(morestuff, "%.70s Error", appname);
  MessageBox(hwnd, stuff, morestuff, MB_ICONERROR | MB_OK);
  sfree(stuff);
}

static BOOL flash_window_ex(DWORD dwFlags, UINT uCount, DWORD dwTimeout)
{
  if (p_FlashWindowEx) {
    FLASHWINFO fi;
    fi.cbSize = sizeof(fi);
    fi.hwnd = hwnd;
    fi.dwFlags = dwFlags;
    fi.uCount = uCount;
    fi.dwTimeout = dwTimeout;
    return (*p_FlashWindowEx) (&fi);
  } else
    return FALSE;       /* shrug */
}

static void flash_window(int mode);
static long next_flash;
static int flashing = 0;

/*
 * Timer for platforms where we must maintain window flashing manually
 * (e.g., Win95).
 */
static void flash_window_timer(void *ctx, unsigned long now)
{
  if (flashing && now == next_flash) {
    flash_window(1);
  }
}

/*
 * Manage window caption / taskbar flashing, if enabled.
 * 0 = stop, 1 = maintain, 2 = start
 */
static void flash_window(int mode)
{
  int beep_ind = conf_get_int(conf, CONF_beep_ind);
  if ((mode == 0) || (beep_ind == B_IND_DISABLED)) {
    /* stop */
    if (flashing) {
      flashing = 0;
      if (p_FlashWindowEx)
        flash_window_ex(FLASHW_STOP, 0, 0);
      else
        FlashWindow(hwnd, FALSE);
    }

  } else if (mode == 2) {
    /* start */
    if (!flashing) {
      flashing = 1;
      if (p_FlashWindowEx) {
        /* For so-called "steady" mode, we use uCount=2, which
         * seems to be the traditional number of flashes used
         * by user notifications (e.g., by Explorer).
         * uCount=0 appears to enable continuous flashing, per
         * "flashing" mode, although I haven't seen this
         * documented. */
        flash_window_ex(FLASHW_ALL | FLASHW_TIMER,
                        (beep_ind == B_IND_FLASH ? 0 : 2),
                        0 /* system cursor blink rate */ );
        /* No need to schedule timer */
      } else {
        FlashWindow(hwnd, TRUE);
        next_flash = schedule_timer(450, flash_window_timer, hwnd);
      }
    }

  } else if ((mode == 1) && (beep_ind == B_IND_FLASH)) {
    /* maintain */
    if (flashing && !p_FlashWindowEx) {
      FlashWindow(hwnd, TRUE);  /* toggle */
      next_flash = schedule_timer(450, flash_window_timer, hwnd);
    }
  }
}

/*
 * Beep.
 */
void do_beep(void *frontend, int mode)
{
  if (mode == BELL_DEFAULT) {
    /*
     * For MessageBeep style bells, we want to be careful of
     * timing, because they don't have the nice property of
     * PlaySound bells that each one cancels the previous
     * active one. So we limit the rate to one per 50ms or so.
     */
    static long lastbeep = 0;
    long beepdiff;

    beepdiff = GetTickCount() - lastbeep;
    if (beepdiff >= 0 && beepdiff < 50)
      return;
    MessageBeep(MB_OK);
    /*
     * The above MessageBeep call takes time, so we record the
     * time _after_ it finishes rather than before it starts.
     */
    lastbeep = GetTickCount();
  } else if (mode == BELL_WAVEFILE) {
    Filename *bell_wavefile = conf_get_filename(conf, CONF_bell_wavefile);
    if (!PlaySound(bell_wavefile->path, NULL, SND_ASYNC | SND_FILENAME)) {
      char buf[sizeof(bell_wavefile->path) + 80];
      char otherbuf[100];
      sprintf(buf, "Unable to play sound file\n%s\n"
              "Using default sound instead", bell_wavefile->path);
      sprintf(otherbuf, "%.70s Sound Error", appname);
      MessageBox(hwnd, buf, otherbuf, MB_OK | MB_ICONEXCLAMATION);
      conf_set_int(conf, CONF_beep, BELL_DEFAULT);
    }
  } else if (mode == BELL_PCSPEAKER) {
    static long lastbeep = 0;
    long beepdiff;

    beepdiff = GetTickCount() - lastbeep;
    if (beepdiff >= 0 && beepdiff < 50)
      return;

    /*
     * We must beep in different ways depending on whether this
     * is a 95-series or NT-series OS.
     */
    if (osVersion.dwPlatformId == VER_PLATFORM_WIN32_NT)
      Beep(800, 100);
    else
      MessageBeep(-1);
    lastbeep = GetTickCount();
  }
  /* Otherwise, either visual bell or disabled; do nothing here */
  if (!term->has_focus) {
    flash_window(2);    /* start */
  }
}

/*
 * Minimise or restore the window in response to a server-side
 * request.
 */
void set_iconic(void *frontend, int iconic)
{
  if (IsIconic(hwnd)) {
    if (!iconic)
      ShowWindow(hwnd, SW_RESTORE);
  } else {
    if (iconic)
      ShowWindow(hwnd, SW_MINIMIZE);
  }
}

/*
 * Move the window in response to a server-side request.
 */
void move_window(void *frontend, int x, int y)
{
  int resize_action = conf_get_int(conf, CONF_resize_action);
  if (resize_action == RESIZE_DISABLED ||
      resize_action == RESIZE_FONT || IsZoomed(hwnd))
    return;

  SetWindowPos(hwnd, NULL, x, y, 0, 0, SWP_NOSIZE | SWP_NOZORDER);
}

/*
 * Move the window to the top or bottom of the z-order in response
 * to a server-side request.
 */
void set_zorder(void *frontend, int top)
{
  if (conf_get_int(conf, CONF_alwaysontop))
    return;     /* ignore */
  SetWindowPos(hwnd, top ? HWND_TOP : HWND_BOTTOM, 0, 0, 0, 0,
               SWP_NOMOVE | SWP_NOSIZE);
}

/*
 * Refresh the window in response to a server-side request.
 */
void refresh_window(void *frontend)
{
  InvalidateRect(hwnd, NULL, TRUE);
}

/*
 * Maximise or restore the window in response to a server-side
 * request.
 */
void set_zoomed(void *frontend, int zoomed)
{
  if (IsZoomed(hwnd)) {
    if (!zoomed)
      ShowWindow(hwnd, SW_RESTORE);
  } else {
    if (zoomed)
      ShowWindow(hwnd, SW_MAXIMIZE);
  }
}

/*
 * Report whether the window is iconic, for terminal reports.
 */
int is_iconic(void *frontend)
{
  return IsIconic(hwnd);
}

/*
 * Report the window's position, for terminal reports.
 */
void get_window_pos(void *frontend, int *x, int *y)
{
  RECT r;
  GetWindowRect(hwnd, &r);
  *x = r.left;
  *y = r.top;
}

/*
 * Report the window's pixel size, for terminal reports.
 */
void get_window_pixels(void *frontend, int *x, int *y)
{
  RECT r;
  GetWindowRect(hwnd, &r);
  *x = r.right - r.left;
  *y = r.bottom - r.top;
}

/*
 * Return the window or icon title.
 */
char *get_window_title(void *frontend, int icon)
{
  return icon ? icon_name : window_name;
}

/*
 * See if we're in full-screen mode.
 */
static int is_full_screen()
{
  if (!IsZoomed(hwnd))
    return FALSE;
  if (GetWindowLongPtr(hwnd, GWL_STYLE) & WS_CAPTION)
    return FALSE;
  return TRUE;
}

/* Get the rect/size of a full screen window using the nearest available
 * monitor in multimon systems; default to something sensible if only
 * one monitor is present. */
static int get_fullscreen_rect(RECT * ss)
{
#if defined(MONITOR_DEFAULTTONEAREST) && !defined(NO_MULTIMON)
  HMONITOR mon;
  MONITORINFO mi;
  mon = MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST);
  mi.cbSize = sizeof(mi);
  GetMonitorInfo(mon, &mi);

  /* structure copy */
  *ss = mi.rcMonitor;
  return TRUE;
#else
/* could also use code like this:
  ss->left = ss->top = 0;
  ss->right = GetSystemMetrics(SM_CXSCREEN);
  ss->bottom = GetSystemMetrics(SM_CYSCREEN);
*/
  return GetClientRect(GetDesktopWindow(), ss);
#endif
}


/*
 * Go full-screen. This should only be called when we are already
 * maximised.
 */
static void make_full_screen()
{
  DWORD style;
  RECT ss;

  assert(IsZoomed(hwnd));

  if (is_full_screen())
    return;

  /* Remove the window furniture. */
  style = (DWORD) GetWindowLongPtr(hwnd, GWL_STYLE);
  style &= ~(WS_CAPTION | WS_BORDER | WS_THICKFRAME);
  if (conf_get_int(conf, CONF_scrollbar_in_fullscreen))
    style |= WS_VSCROLL;
  else
    style &= ~WS_VSCROLL;
  SetWindowLongPtr(hwnd, GWL_STYLE, style);

  /* Resize ourselves to exactly cover the nearest monitor. */
  get_fullscreen_rect(&ss);
  SetWindowPos(hwnd, HWND_TOP, ss.left, ss.top,
               ss.right - ss.left, ss.bottom - ss.top, SWP_FRAMECHANGED);

  /* We may have changed size as a result */

  reset_window(0);

  /* Tick the menu item in the System and context menus. */
  {
    int i;
    for (i = 0; i < lenof(popup_menus); i++)
      CheckMenuItem(popup_menus[i].menu, IDM_FULLSCREEN, MF_CHECKED);
  }
}

/*
 * Clear the full-screen attributes.
 */
static void clear_full_screen()
{
  DWORD oldstyle, style;

  /* Reinstate the window furniture. */
  style = oldstyle = (DWORD) GetWindowLongPtr(hwnd, GWL_STYLE);
  style |= WS_CAPTION | WS_BORDER;
  if (conf_get_int(conf, CONF_resize_action) == RESIZE_DISABLED)
    style &= ~WS_THICKFRAME;
  else
    style |= WS_THICKFRAME;
  if (conf_get_int(conf, CONF_scrollbar))
    style |= WS_VSCROLL;
  else
    style &= ~WS_VSCROLL;
  if (style != oldstyle) {
    SetWindowLongPtr(hwnd, GWL_STYLE, style);
    SetWindowPos(hwnd, NULL, 0, 0, 0, 0,
                 SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_FRAMECHANGED);
  }

  /* Untick the menu item in the System and context menus. */
  {
    int i;
    for (i = 0; i < lenof(popup_menus); i++)
      CheckMenuItem(popup_menus[i].menu, IDM_FULLSCREEN, MF_UNCHECKED);
  }
}

/*
 * Toggle full-screen mode.
 */
static void flip_full_screen()
{
  if (is_full_screen()) {
    ShowWindow(hwnd, SW_RESTORE);
  } else if (IsZoomed(hwnd)) {
    make_full_screen();
  } else {
    SendMessage(hwnd, WM_FULLSCR_ON_MAX, 0, 0);
    ShowWindow(hwnd, SW_MAXIMIZE);
  }
}

void frontend_keypress(void *handle)
{
  /*
   * Keypress termination in non-Close-On-Exit mode is not
   * currently supported in PuTTY proper, because the window
   * always has a perfectly good Close button anyway. So we do
   * nothing here.
   */
  return;
}

int from_backend(void *frontend, int is_stderr, const char *data, int len)
{
  return term_data(term, is_stderr, data, len);
}

int from_backend_untrusted(void *frontend, const char *data, int len)
{
  return term_data_untrusted(term, data, len);
}

int from_backend_eof(void *frontend)
{
  return TRUE;  /* do respond to incoming EOF with outgoing */
}

int get_userpass_input(prompts_t * p, const unsigned char *in, int inlen)
{
  int ret;
  ret = cmdline_get_passwd_input(p, in, inlen);
  if (ret == -1)
    ret = term_get_userpass_input(term, p, in, inlen);
  return ret;
}

void agent_schedule_callback(void (*callback) (void *, void *, int),
                             void *callback_ctx, void *data, int len)
{
  struct agent_callback *c = snew(struct agent_callback);
  c->callback = callback;
  c->callback_ctx = callback_ctx;
  c->data = data;
  c->len = len;
  PostMessage(hwnd, WM_AGENT_CALLBACK, 0, (LPARAM) c);
}

void reset_colour(void *frontend, int number)
{
  int i = number;
  if (number < 0) {
    if (pal)
      for (i = 0; i < NALLCOLOURS; i++)
        colours[i] = PALETTERGB(defpal[i].rgbtRed,
                                defpal[i].rgbtGreen,
                                defpal[i].rgbtBlue);
    else
      for (i = 0; i < NALLCOLOURS; i++)
        colours[i] = RGB(defpal[i].rgbtRed,
                         defpal[i].rgbtGreen, defpal[i].rgbtBlue);
  } else if (number < NALLCOLOURS) {
    if (pal)
      colours[i] = PALETTERGB(defpal[i].rgbtRed,
                              defpal[i].rgbtGreen,
                              defpal[i].rgbtBlue);
    else
      colours[i] = RGB(defpal[i].rgbtRed,
                       defpal[i].rgbtGreen, defpal[i].rgbtBlue);
  }
  InvalidateRect(hwnd, NULL, TRUE);
  return;
}

void set_colour(void *frontend, int number, int colour)
{
  if (number >= NALLCOLOURS) {
    return;
  }
  colours[number] = RGB((colour >> 16) & 0xff,
                        (colour >> 8) & 0xff,
                        (colour >> 0) & 0xff);
  InvalidateRect(hwnd, NULL, TRUE);
  return;
}

int get_colour(void *frontend, int number)
{
  int r, g, b;

  if (number >= NALLCOLOURS) {
    return 0;
  }
  r = GetRValue(colours[number]);
  g = GetGValue(colours[number]);
  b = GetBValue(colours[number]);
  return (r << 16) + (g << 8) + b;
}

// d2d

int window_begin()
{
  int ret = d2d_begin();
  if (ret == 0) {
    d2d_clear();

    for (int i = 0; i < term->rows; i++) {
      for (int j = 0; j < term->cols; j++) {
        term->disptext[i]->chars[j].attr |= ATTR_INVALID;
      }
    }
  }
  return ret;
}

void window_end()
{
  d2d_end();
}

static void d2d_create()
{
  D2DBG("d2d_create:\n");

  d2d_release();

  D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED,
                    __uuidof(ID2D1Factory), 0, (void **) &d2dF);
  float dashes[] = { 1.0f, 2.0f };
  D2D1_STROKE_STYLE_PROPERTIES properties =
    D2D1::StrokeStyleProperties(D2D1_CAP_STYLE_FLAT,
                                D2D1_CAP_STYLE_FLAT,
                                D2D1_CAP_STYLE_SQUARE,
                                D2D1_LINE_JOIN_MITER,
                                1.0f,
                                D2D1_DASH_STYLE_CUSTOM,
                                0.0f);
  d2dF->CreateStrokeStyle(properties, dashes, ARRAYSIZE(dashes), &d2dSS);
}

static void d2d_release()
{
  d2d_deinit();

  if (d2dF) {
    d2dF->Release();
    d2dF = NULL;
  }
  if (d2dSS) {
    d2dSS->Release();
    d2dSS = NULL;
  }
}

static void d2d_init()
{
  D2DBG("d2d_init:\n");

  d2d_deinit();

  RECT rc;
  GetClientRect(hwnd, &rc);
  D2D1_SIZE_U size = D2D1::SizeU(rc.right - rc.left, rc.bottom - rc.top);
  const D2D1_PIXEL_FORMAT format =
    D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM,
                      //D2D1_ALPHA_MODE_UNKNOWN);
                      //D2D1_ALPHA_MODE_STRAIGHT);
                      // D2D1_ALPHA_MODE_IGNORE);
                      D2D1_ALPHA_MODE_PREMULTIPLIED);
  CONST D2D1_RENDER_TARGET_PROPERTIES targetProperties =
    D2D1::RenderTargetProperties(D2D1_RENDER_TARGET_TYPE_DEFAULT, format);
  CONST D2D1_HWND_RENDER_TARGET_PROPERTIES windowProperties =
    D2D1::HwndRenderTargetProperties(hwnd, size,
                                     // D2D1_PRESENT_OPTIONS_NONE);
                                     D2D1_PRESENT_OPTIONS_IMMEDIATELY);
  d2dF->CreateHwndRenderTarget(targetProperties, windowProperties, &d2dRT);

  DWRITE_RENDERING_MODE rendering_mode_dw = DW_RENDERING_MODE(rendering_mode);
  if (D2D_FONT_QUALITY(font_quality) == D2D1_TEXT_ANTIALIAS_MODE_ALIASED) {
    rendering_mode_dw = DWRITE_RENDERING_MODE_ALIASED;
  }
  if ((D2D_FONT_QUALITY(font_quality) ==
       D2D1_TEXT_ANTIALIAS_MODE_CLEARTYPE) &&
      (rendering_mode_dw == DWRITE_RENDERING_MODE_OUTLINE)) {
    rendering_mode_dw = DWRITE_RENDERING_MODE_DEFAULT;
  }

  HMONITOR mon = MonitorFromWindow(hwnd, MONITOR_DEFAULTTONEAREST);
  IDWriteRenderingParams *dwrpm = NULL;
  IDWriteRenderingParams *dwrpc = NULL;
  dwF->CreateMonitorRenderingParams(mon, &dwrpm);
  dwF->CreateCustomRenderingParams(     //dwrpm->GetGamma(),
                                    // dwrpm->GetEnhancedContrast(),
                                    // dwrpm->GetClearTypeLevel(),
                                    (FLOAT) gamma / 1000.0f,
                                    (FLOAT) enhanced_contrast / 100.0f,
                                    (FLOAT) cleartype_level / 100.0f,
                                    dwrpm->GetPixelGeometry(),
                                    rendering_mode_dw, &dwrpc);
  d2dRT->SetTextRenderingParams(dwrpc);
  d2dRT->SetDpi(96.0f, 96.0f);
  dwrpm->Release();
  dwrpc->Release();

  static const int CONF_alphas_pc[4][2] = {
    {CONF_alphas_pc_cursor_active,
     CONF_alphas_pc_cursor_inactive},
    {CONF_alphas_pc_defauly_fg_active,
     CONF_alphas_pc_defauly_fg_inactive},
    {CONF_alphas_pc_degault_bg_active,
     CONF_alphas_pc_degault_bg_inactive},
    {CONF_alphas_pc_bg_active,
     CONF_alphas_pc_bg_inactive}
  };
  int i, j;
  for (i = 0; i < 4; i++) {
    for (j = 0; j < 2; j++) {
      if (conf_get_int(conf, CONF_alphas_pc[i][j]) > 100) {
        conf_set_int(conf, CONF_alphas_pc[i][j], 100);
      }
      if (conf_get_int(conf, CONF_alphas_pc[i][j]) < 0) {
        conf_set_int(conf, CONF_alphas_pc[i][j], 0);
      }
      alphas[i][j] = (FLOAT) conf_get_int(conf, CONF_alphas_pc[i][j]) / 100;
      if ((alphas[i][j] == 0) && (bg_effect == BG_PLANE)) {
        alphas[i][j] = (FLOAT) 0.01;
      }
    }
  }

  d2dRT->SetTextAntialiasMode(D2D_FONT_QUALITY(font_quality));

  d2dRT->
    CreateSolidColorBrush(D2D1::
                          ColorF(0.0f, 0.0f, 0.0f,
                                 alphas[ALPHA_DEFAULT_FG][BG_ACTIVE]),
                          &d2dSCBfg);
  CONST D2D1_BRUSH_PROPERTIES brushProperties =
    D2D1::BrushProperties(1.0f, D2D1::Matrix3x2F::Identity());
  d2dRT->
    CreateSolidColorBrush(D2D1::
                          ColorF(0.0f, 0.0f, 0.0f,
                                 alphas[ALPHA_BG][BG_ACTIVE]), brushProperties,
                          &d2dSCBbg);
  d2dRT->
    CreateSolidColorBrush(D2D1::
                          ColorF(0.0f, 0.0f, 0.0f,
                                 alphas[ALPHA_CURSOR][BG_ACTIVE]), &d2dSCBc);
}

static void d2d_deinit()
{
  if (d2dRT) {
    d2dRT->Release();
    d2dRT = NULL;
  }
  if (d2dSCBfg) {
    d2dSCBfg->Release();
    d2dSCBfg = NULL;
  }
  if (d2dSCBbg) {
    d2dSCBbg->Release();
    d2dSCBbg = NULL;
  }
  if (d2dSCBc) {
    d2dSCBc->Release();
    d2dSCBc = NULL;
  }
}

static int d2d_begin()
{
  if (d2dF != NULL && d2dRT == NULL) {
    // re-create the render target and related resources.
    d2d_init();
  }

  if (!d2dRT) {
    // TODO: define err code.
    return 1;
  }
  d2dRT->BeginDraw();
  return 0;
}

static void d2d_end()
{
  if (!d2dRT) {
    return;
  }
  if (d2dRT->EndDraw() == D2DERR_RECREATE_TARGET) {
    // release the render target and related resources(keep d2dF).
    d2d_deinit();
  }
}

static void d2d_clear()
{
  // D2DBG("d2d_clear:\n");

  if ((!d2dRT) || (d2dRT->CheckWindowState() & D2D1_WINDOW_STATE_OCCLUDED)) {
    D2DBG("d2d_clear: skip\n");
    return;
  }

  D2D1_RECT_F rect;
  RECT cr;
  GetClientRect(hwnd, &cr);

  d2dRT->Clear(D2D1::ColorF(0.0f, 0.0f, 0.0f, 0.0f));
  d2dSCBbg->
    SetColor(D2D1::ColorF(colours[258], alphas[ALPHA_DEFAULT_BG][BG_ACTIVE]));

  rect = D2D1::RectF((FLOAT) cr.left,
                     (FLOAT) cr.top, (FLOAT) cr.right, (FLOAT) cr.bottom);
  //  d2dRT->FillRectangle(&rect, d2dSCBbg);

  // if (d2dBM) {
  //   d2dRT->DrawBitmap(d2dBM, rect, alphas[ALPHA_DEFAULT_BG][BG_ACTIVE]);
  // }

  wp_draw(&rect);
  // if (d2dWP && d2dRT) {
  //   d2dRT->DrawBitmap(d2dWP, rect, alphas[ALPHA_DEFAULT_BG][BG_ACTIVE]);
  // }

  return;

  if (border_style != BS_GRADATION) {
    FLOAT w = (FLOAT) window_border / 2;
    FLOAT l = 0.0f + w;
    FLOAT t = 0.0f + w;
    FLOAT r = (FLOAT) cr.right - w;
    FLOAT b = (FLOAT) cr.bottom - w;

    rect = D2D1::RectF(l, t, r, b);
    if (border_style == BS_ROUNDED) {
      D2D1_ROUNDED_RECT rrect = { rect, w, w };
      d2dRT->DrawRoundedRectangle(&rrect, d2dSCBbg, (FLOAT) window_border);
    } else {
      d2dRT->DrawRectangle(&rect, d2dSCBbg, (FLOAT) window_border);
    }
  } else {
    int grad = window_border - 1;
    if (grad < 1) {
      return;
    }

    FLOAT w = 1.0f / 2;
    FLOAT l = 0.0f + w;
    FLOAT t = 0.0f + w;
    FLOAT r = (FLOAT) cr.right - w;
    FLOAT b = (FLOAT) cr.bottom - w;

    for (int i = grad; i != 0; i--) {
      rect = D2D1::RectF(l, t, r, b);
      FLOAT alpha =
        alphas[ALPHA_DEFAULT_BG][BG_ACTIVE] * (grad - i + 1) / grad;
      d2dSCBbg->SetColor(D2D1::ColorF(colours[258], alpha));
      d2dRT->DrawRectangle(&rect, d2dSCBbg, 1.0f);
      l = l + 1.0f;
      t = t + 1.0f;
      r = r - 1.0f;
      b = b - 1.0f;
    }
    for (int i = window_border - grad; i != 0; i--) {
      rect = D2D1::RectF(l, t, r, b);
      d2dSCBbg->
        SetColor(D2D1::
                 ColorF(colours[258], alphas[ALPHA_DEFAULT_BG][BG_ACTIVE]));
      d2dRT->DrawRectangle(&rect, d2dSCBbg, 1.0f);
      l = l + 1.0f;
      t = t + 1.0f;
      r = r - 1.0f;
      b = b - 1.0f;
    }
  }

  if (offset_height - window_border > 0) {
    rect = D2D1::RectF((FLOAT) window_border,
                       (FLOAT) window_border,
                       (FLOAT) cr.right - window_border,
                       (FLOAT) offset_height);
    d2dRT->FillRectangle(&rect, d2dSCBbg);
    rect = D2D1::RectF((FLOAT) window_border,
                       (FLOAT) cr.bottom - offset_height,
                       (FLOAT) cr.right - window_border,
                       (FLOAT) cr.bottom - window_border);
    d2dRT->FillRectangle(&rect, d2dSCBbg);
  }
  if (offset_width - window_border > 0) {
    d2dSCBbg->
      SetColor(D2D1::
               ColorF(colours[258], alphas[ALPHA_DEFAULT_BG][BG_ACTIVE]));
    rect =
      D2D1::RectF((FLOAT) window_border, (FLOAT) offset_height,
                  (FLOAT) offset_width, (FLOAT) cr.bottom - offset_height);
    d2dRT->FillRectangle(&rect, d2dSCBbg);
    rect = D2D1::RectF((FLOAT) cr.right - offset_width,
                       (FLOAT) offset_height,
                       (FLOAT) cr.right - window_border,
                       (FLOAT) cr.bottom - offset_height);
    d2dRT->FillRectangle(&rect, d2dSCBbg);
  }

}

static void d2d_resize()
{
  D2DBG("d2d_resize:\n");

  if (!d2dRT) {
    return;
  }

  RECT rc;
  GetClientRect(hwnd, &rc);
  D2D1_SIZE_U size = D2D1::SizeU(rc.right - rc.left, rc.bottom - rc.top);
  d2dRT->Resize(size);

  bg_resize(1);
}

static LCID getLCID(DWORD CharSet)
{
  switch (CharSet) {
  case ANSI_CHARSET:
    return 0x0409;
  case DEFAULT_CHARSET:
    return LOCALE_USER_DEFAULT;
    // case SYMBOL_CHARSET: return 0x0;
  case SHIFTJIS_CHARSET:
    return 0x411;
  case HANGEUL_CHARSET:
    return 0x412;
  case GB2312_CHARSET:
    return 0x804;
  case CHINESEBIG5_CHARSET:
    return 0x404;
    // case OEM_CHARSET: return 0x0;
  case JOHAB_CHARSET:
    return 0x812;
  case HEBREW_CHARSET:
    return 0x40d;
  case ARABIC_CHARSET:
    return 0x01;
  case GREEK_CHARSET:
    return 0x408;
  case TURKISH_CHARSET:
    return 0x41f;
  case VIETNAMESE_CHARSET:
    return 0x42a;
  case THAI_CHARSET:
    return 0x41e;
  case EASTEUROPE_CHARSET:
    return 0x405;
  case RUSSIAN_CHARSET:
    return 0x419;
    // case MAC_CHARSET: return 0xFFF;
  case BALTIC_CHARSET:
    return 0x425;
  }
  return LOCALE_USER_DEFAULT;
}


static void dw_create()
{
  D2DBG("dw_create:\n");

  dw_release();

  DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED,
                      __uuidof(IDWriteFactory), (IUnknown **) & dwF);
}

static void dw_release()
{
  dw_deinit();

  if (dwF) {
    dwF->Release();
    dwF = NULL;
  }
}

static void dw_init(int size)
{
  D2DBG("dw_init:\n");

  dw_deinit();

  //
  WCHAR wfontname[64];
  WCHAR wlocalename[LOCALE_NAME_MAX_LENGTH];
  FontSpec *font;

  font = conf_get_fontspec(conf, CONF_font);
  MultiByteToWideChar(CP_UTF8, 0, font->name, -1, (LPWSTR) & wfontname, 64);
  GetLocaleInfoW(getLCID(font->charset), LOCALE_SNAME,
                 &wlocalename[0], ARRAYSIZE(wlocalename));
  dw_fontface(wfontname, font->charset, size, FW_NORMAL,
              &dwFF[FF_NORMAL][FF_NORMAL]);
  dw_fontface(wfontname, font->charset, size, FW_BOLD,
              &dwFF[FF_NORMAL][FF_BOLD]);
  D2DBG("  wfontname=%ls charset=%d wlocalename=%ls\n",
        wfontname, font->charset, wlocalename);


  if (use_widefont && fonts[FONT_WIDE]) {
    font = conf_get_fontspec(conf, CONF_widefont);
    MultiByteToWideChar(CP_UTF8, 0, font->name, -1,
                        (LPWSTR) & wfontname, 64);
    GetLocaleInfoW(getLCID(font->charset), LOCALE_SNAME,
                   &wlocalename[0], ARRAYSIZE(wlocalename));
    dw_fontface(wfontname, font->charset, size, FW_NORMAL,
                &dwFF[FF_WIDE][FF_NORMAL]);
    dw_fontface(wfontname, font->charset, size, FW_BOLD,
                &dwFF[FF_WIDE][FF_BOLD]);
    D2DBG("  wfontname=%ls charset=%d wlocalename=%ls\n",
          wfontname, font->charset, wlocalename);
  }

  if (use_altfont) {
    font = conf_get_fontspec(conf, CONF_altfont);
    MultiByteToWideChar(CP_UTF8, 0, font->name, -1,
                        (LPWSTR) & wfontname, 64);
    GetLocaleInfoW(getLCID(font->charset), LOCALE_SNAME,
                   &wlocalename[0], ARRAYSIZE(wlocalename));
    dw_fontface(wfontname, font->charset, size, FW_NORMAL,
                &dwFF[FF_ALT][FF_NORMAL]);
    dw_fontface(wfontname, font->charset, size, FW_BOLD,
                &dwFF[FF_ALT][FF_BOLD]);
  }
}

static void dw_deinit()
{
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 2; j++) {
      if (dwFF[i][j]) {
        dwFF[i][j]->Release();
        dwFF[i][j] = NULL;
      }
    }
  }

  memset(dw_width, 0, sizeof(FLOAT) * 3 * 2 * 0x10000);
}

static void
dw_fontface(const WCHAR * name, int charset, int size, int weight,
            IDWriteFontFace ** fontface)
{
  D2DBG("dw_fontface: %ls\n", name);

  HFONT hf = CreateFontW(-size, 0, 0, 0, weight, FALSE, FALSE, FALSE,
                         charset,
                         OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                         FONT_QUALITY(font_quality),
                         FF_DONTCARE,
                         name);
  HDC hdc = GetDC(hwnd);
  SelectObject(hdc, hf);
  LOGFONTW lfw;
  GetObjectW(hf, sizeof(LOGFONTW), &lfw);
  // TEXTMETRIC tm;
  // GetTextMetrics(hdc, &tm);

  IDWriteGdiInterop *dw_gi;
  dwF->GetGdiInterop(&dw_gi);
  IDWriteFont *dw_f;
  HRESULT hr = dw_gi->CreateFontFromLOGFONT(&lfw, &dw_f);
  dw_f->CreateFontFace(fontface);

#if 0
  DWRITE_FONT_METRICS fm;
  dw_f->GetMetrics(&fm);
  D2DBG("dw_fontface: designUnitsPerEm=%d\n", fm.designUnitsPerEm);
  D2DBG("     metric: size=%f a+cH=%f capH=%f xH=%f\n",
        (FLOAT) size,
        (FLOAT) (fm.ascent + fm.descent) * size / fm.designUnitsPerEm,
        (FLOAT) fm.capHeight * size / fm.designUnitsPerEm,
        (FLOAT) fm.xHeight * size / fm.designUnitsPerEm);
  D2DBG("           : asc=%f des=%f gap=%f\n",
        (FLOAT) fm.ascent * size / fm.designUnitsPerEm,
        (FLOAT) fm.descent * size / fm.designUnitsPerEm,
        (FLOAT) fm.lineGap * size / fm.designUnitsPerEm);
  D2DBG("           : uPos=%f uThick=%f sPos=%f sThick=%f\n",
        (FLOAT) fm.underlinePosition * size / fm.designUnitsPerEm,
        (FLOAT) fm.underlineThickness * size / fm.designUnitsPerEm,
        (FLOAT) fm.strikethroughPosition * size / fm.designUnitsPerEm,
        (FLOAT) fm.strikethroughThickness * size / fm.designUnitsPerEm);
  D2DBG("           : size=%d a+cH=%d capHeight=%d xHeight=%d\n",
        size, fm.ascent + fm.descent, fm.capHeight, fm.xHeight);
  D2DBG("           : asc=%d des=%d gap=%d\n",
        fm.ascent, fm.descent, fm.lineGap);
  D2DBG("           : uPos=%d uThick=%d sPos=%d sThick=%d\n",
        fm.underlinePosition,
        fm.underlineThickness,
        fm.strikethroughPosition, fm.strikethroughThickness);
#endif

#if 0
  (*fontface)->GetGdiCompatibleMetrics((FLOAT) size, pixelsPerDip, NULL, &fm);
  D2DBG("        gdi: size=%f a+cH=%f capH=%f xH=%f\n",
        (FLOAT) size,
        (FLOAT) (fm.ascent + fm.descent) * size / fm.designUnitsPerEm,
        (FLOAT) fm.capHeight * size / fm.designUnitsPerEm,
        (FLOAT) fm.xHeight * size / fm.designUnitsPerEm);
  D2DBG("           : asc=%f des=%f gap=%f\n",
        (FLOAT) fm.ascent * size / fm.designUnitsPerEm,
        (FLOAT) fm.descent * size / fm.designUnitsPerEm,
        (FLOAT) fm.lineGap * size / fm.designUnitsPerEm);
  D2DBG("           : uPos=%f uThick=%f sPos=%f sThick=%f\n",
        (FLOAT) fm.underlinePosition * size / fm.designUnitsPerEm,
        (FLOAT) fm.underlineThickness * size / fm.designUnitsPerEm,
        (FLOAT) fm.strikethroughPosition * size / fm.designUnitsPerEm,
        (FLOAT) fm.strikethroughThickness * size / fm.designUnitsPerEm);
  D2DBG("           : size=%d a+cH=%d capHeight=%d xHeight=%d\n",
        size, fm.ascent + fm.descent, fm.capHeight, fm.xHeight);
  D2DBG("           : asc=%d des=%d gap=%d\n",
        fm.ascent, fm.descent, fm.lineGap);
  D2DBG("           : uPos=%d uThick=%d sPos=%d sThick=%d\n",
        fm.underlinePosition,
        fm.underlineThickness,
        fm.strikethroughPosition, fm.strikethroughThickness);
#endif

  SelectObject(hdc, GetStockObject(SYSTEM_FONT));
  DeleteObject(hf);

  dw_f->Release();
  dw_gi->Release();
}

static FLOAT dw_getwidth(UINT16 index, IDWriteFontFace * fontface)
{
  DWRITE_MATRIX dm = { 1, 0, 0, 1, 0, 0 };
  DWRITE_FONT_METRICS fm;
  fontface->GetGdiCompatibleMetrics((FLOAT) font_size,
                                    pixelsPerDip, NULL, &fm);
  DWRITE_GLYPH_METRICS gm;
  fontface->GetGdiCompatibleGlyphMetrics((FLOAT) font_size,
                                         pixelsPerDip,
                                         &dm, TRUE, &index, 1, &gm, FALSE);
  return (FLOAT) gm.advanceWidth * font_size / fm.designUnitsPerEm;
}

static void
dw_textout(int x, int y, UINT opt, const RECT * rc,
           WCHAR * str, UINT len, const int *dx, int wide,
           unsigned long long attr)
{
  if (!d2dRT) {
    return;
  }

  RECT rc2 = *rc;
  int baseline_offset_now = wide ? baseline_offset_fw : baseline_offset;
  int width = *dx;
  for (UINT i = 1; i < len; i++) {
    if (width) {
      break;
    } else {
      width = dx[i];
    }
  }

  //
  if (opt & ETO_OPAQUE) {
    D2D1_RECT_F r = D2D1::RectF((FLOAT) rc2.left,
                                (FLOAT) rc2.top,
                                (FLOAT) rc2.right,
                                (FLOAT) rc2.bottom);
    d2dRT->FillRectangle(&r, d2dSCBbg);
  }

  if (attr & ATTR_UNDER) {
    D2D1_POINT_2F p0 = D2D1::Point2F((FLOAT) rc2.left,
                                     (FLOAT) rc2.top + font_ascent -
                                     font_underline - baseline_offset_now + 0.5f);
    D2D1_POINT_2F p1 = D2D1::Point2F((FLOAT) rc2.right,
                                     (FLOAT) rc2.top + font_ascent -
                                     font_underline - baseline_offset_now + 0.5f);
    d2dRT->DrawLine(p0, p1, d2dSCBfg, 1.0f);
  }
  //
  static UINT wlen = 512;
  static UINT16 *indices[3] =
    { new UINT16[wlen], new UINT16[wlen], new UINT16[wlen] };
  static FLOAT *advances = new FLOAT[wlen];
  static DWRITE_GLYPH_OFFSET *offsets = new DWRITE_GLYPH_OFFSET[wlen];
  static UINT16 *clusters = new UINT16[wlen];
  static DWRITE_SHAPING_TEXT_PROPERTIES *textprops =
    new DWRITE_SHAPING_TEXT_PROPERTIES[wlen];
  static DWRITE_SHAPING_GLYPH_PROPERTIES *glyphprops =
    new DWRITE_SHAPING_GLYPH_PROPERTIES[wlen];
  wlen = 256;
  if (wlen < len) {
    if (offsets) {
      delete[]indices[0];
      delete[]indices[1];
      delete[]indices[2];
      delete[]advances;
      delete[]offsets;
      delete[]clusters;
      delete[]textprops;
      delete[]glyphprops;
    }
    int l = len * 2;
    indices[0] = new UINT16[l];
    indices[1] = new UINT16[l];
    indices[2] = new UINT16[l];
    advances = new FLOAT[l];
    offsets = new DWRITE_GLYPH_OFFSET[l];
    clusters = new UINT16[l];
    textprops = new DWRITE_SHAPING_TEXT_PROPERTIES[l];
    glyphprops = new DWRITE_SHAPING_GLYPH_PROPERTIES[l];
    wlen = len;
  }
  //
  wide = (wide && use_widefont && dwFF[FF_WIDE][FF_NORMAL]) ?
    FF_WIDE : FF_NORMAL;
  int weight = (attr & ATTR_BOLD) ? FF_BOLD : FF_NORMAL;
  int alt = (dwFF[FF_ALT][FF_NORMAL]) ? FF_ALT : wide;

  static IDWriteTextAnalyzer *analyzer = NULL;
  if (!analyzer) {
    dwF->CreateTextAnalyzer(&analyzer);
  }
  static const DWRITE_SCRIPT_ANALYSIS script =
    { 0, DWRITE_SCRIPT_SHAPES_DEFAULT };
  UINT32 remain;

  analyzer->GetGlyphs(str, len, dwFF[wide][weight],
                      FALSE, FALSE,
                      &script,
                      NULL, NULL, NULL, NULL, 0,
                      len * 2,
                      clusters, textprops, indices[wide], glyphprops, &remain);

  for (UINT i = 0; i < remain; i++) {
    if (!indices[wide][i]) {
      analyzer->GetGlyphs(str, len, dwFF[alt][weight],
                          FALSE, FALSE,
                          &script,
                          NULL, NULL, NULL, NULL, 0,
                          len * 2,
                          clusters,
                          textprops, indices[alt], glyphprops, &remain);
      break;
    }
  }

  //
  UINT16 *index[3] = { indices[0], indices[1], indices[2] };
  UINT i;
  FLOAT width_i;
  FLOAT width_0;
  int face_i;
  int face_0;
  UINT16 index_0;
  UINT16 index_i;
  bool large_0;
  bool large_i;

  while (remain) {
    i = 0;
    face_0 = (index[wide][0]) ? wide : alt;
    index_0 = index[face_0][0];

    if (dw_width[face_0][weight][index_0] == 0) {
      dw_width[face_0][weight][index_0] =
        dw_getwidth(index_0, dwFF[face_0][weight]);
    }
    width_0 = dw_width[face_0][weight][index_0];
    large_0 = (width_0 > width);

    advances[0] = (large_0) ? width_0 : width;
    offsets[0].advanceOffset = (large_0) ? 0 : (width - width_0) / 2;
    offsets[0].ascenderOffset = 0;

    //
    for (i = 1; i < remain; i++) {

      face_i = (index[wide][i]) ? wide : alt;
      index_i = index[face_i][i];

      if (face_0 != face_i) {
        break;
      }

      if (dw_width[face_i][weight][index_i] == 0) {
        dw_width[face_i][weight][index_i] =
          dw_getwidth(index_i, dwFF[face_i][weight]);
      }
      width_i = dw_width[face_i][weight][index_i];
      large_i = (width_i > width);

      if ((!large_0 && large_i) || (large_0 && (width_0 != width_i))) {
        break;
      }

      advances[i] = (large_i) ? width_i : width;
      offsets[i].advanceOffset = (large_i) ? 0 : (width - width_i) / 2;
      offsets[i].ascenderOffset = 0;
    }

    //
    if (large_0) {
      D2D1_MATRIX_3X2_F scale =
        D2D1::Matrix3x2F::Scale(D2D1::Size(width / width_0, 1.0f),
                                D2D1::Point2F((FLOAT) rc2.left, 0.0f));
      d2dRT->SetTransform(scale);
    }

    D2D1_POINT_2F origin = D2D1::Point2F((FLOAT) rc2.left,
                                         (FLOAT) rc2.top + font_ascent -
                                         baseline_offset_now);

    DWRITE_GLYPH_RUN g;
    g.fontFace = dwFF[face_0][weight];
    g.fontEmSize = (FLOAT) font_size;
    g.glyphCount = i;
    g.glyphIndices = index[face_0];
    g.glyphAdvances = advances;
    g.glyphOffsets = offsets;
    g.isSideways = FALSE;
    g.bidiLevel = 0;

    d2dRT->DrawGlyphRun(origin, &g, d2dSCBfg, DWRITE_MEASURING_MODE_NATURAL);
    // DWRITE_MEASURING_MODE_GDI_NATURAL);

    if (large_0) {
      d2dRT->SetTransform(D2D1::Matrix3x2F::Identity());
    }

    remain -= i;
    index[0] += i;
    index[1] += i;
    index[2] += i;
    rc2.left += width * i;
  }
}

/* Background */
/* Transparency */

static void bg_create()
{
  bg_release();

  bm_create();
  wp_create();

  bg_glass();
}

static void bg_release()
{
  wp_release();
  bm_release();
}

static void bm_create()
{
  D2DBG("bm_create:\n");

  bm_release();

  if ((bg_wallpaper == BG_NONE) | (bg_wallpaper == BG_DESKTOP)) {
    return;
  }

  char *wp_file = conf_get_filename(conf, CONF_wp_file)->path;
  if (wp_file == NULL || strlen(wp_file) == 0) {
    return;
  }

  IWICImagingFactory *wic;
  IWICBitmapDecoder *dec;
  IWICBitmapFrameDecode *frame;
  IWICFormatConverter *converter;

  WCHAR wp_path[MAX_PATH];
  MultiByteToWideChar(CP_UTF8, 0, wp_file, -1,
                      (LPWSTR) & wp_path, MAX_PATH);
  CoCreateInstance(CLSID_WICImagingFactory, NULL, CLSCTX_INPROC_SERVER,
                   IID_IWICImagingFactory, reinterpret_cast < void **>(&wic));
  HRESULT hr = wic->CreateDecoderFromFilename(wp_path, NULL,
                                              GENERIC_READ,
                                              WICDecodeMetadataCacheOnLoad,
                                              &dec);
  if (!SUCCEEDED(hr)) {
    wic->Release();
    nonfatal("\"%s\" not found.", wp_file);
    return;
  }

  dec->GetFrame(0, &frame);
  wic->CreateFormatConverter(&converter);
  converter->Initialize(frame, GUID_WICPixelFormat32bppPBGRA,
                        WICBitmapDitherTypeNone, NULL, 0.f,
                        WICBitmapPaletteTypeMedianCut);
  d2dRT->CreateBitmapFromWicBitmap(converter, NULL, &d2dBM);

  converter->Release();
  frame->Release();
  dec->Release();
  wic->Release();

  D2D1_SIZE_U s = d2dBM->GetPixelSize();
  bm_width = s.width;
  bm_height = s.height;

  return;
}

static void bm_release()
{
  if (d2dBM) {
    d2dBM->Release();
    d2dBM = NULL;
  }
}

static void wp_create()
{
  D2DBG("wp_create\n");

  wp_release();

  if (d2dBM == NULL) {
    return;
  }

  ID2D1BitmapRenderTarget *brt;
  ID2D1Bitmap *wp;

  int win_width = 0;
  int win_height = 0;
  int stretch_width = 0;
  int stretch_height = 0;
  int offset_x = 0;
  int offset_y = 0;

  int stretch = 0;
  RECT rc;

  enum {
    STRETCH_NONE, STRETCH_WIDTH, STRETCH_HEIGHT, STRETCH_BOTH
  };

  if (bg_wallpaper == BG_FILE) {
    GetClientRect(hwnd, &rc);
    win_width = rc.right - rc.left;
    win_height = rc.bottom - rc.top;
  } else if (bg_wallpaper == BG_FILE_DESKTOP) {
    win_width = GetSystemMetrics(SM_CXVIRTUALSCREEN);
    win_height = GetSystemMetrics(SM_CYVIRTUALSCREEN);
    rc.left = 0;
    rc.top = 0;
    rc.right = win_width;
    rc.bottom = win_height;
  } else {
    return;
  }

  d2dRT->CreateCompatibleRenderTarget(D2D1::SizeF((FLOAT) win_width,
                                                  (FLOAT) win_height), &brt);

  brt->BeginDraw();
  brt->Clear(D2D1::ColorF(0.0f, 0.0f, 0.0f, 0.0f));
  d2dSCBbg->SetColor(D2D1::ColorF(colours[258], 1.0f));
  brt->FillRectangle(D2D1::RectF((FLOAT) 0, (FLOAT) 0,
                                 (FLOAT) win_width, (FLOAT) win_height),
                     d2dSCBbg);

  switch (wp_position) {
  case WP_FILL:
    stretch = ((win_width * bm_height) > (win_height * bm_width)) ?
      STRETCH_WIDTH : STRETCH_HEIGHT;
    break;
  case WP_FIT:
    stretch = ((win_width * bm_height) > (win_height * bm_width)) ?
      STRETCH_HEIGHT : STRETCH_WIDTH;
    break;
  case WP_STRETCH:
    stretch = STRETCH_BOTH;
    break;
  case WP_TILE:
  case WP_FIX:
    stretch = STRETCH_NONE;
    break;
  }

  switch (stretch) {
  case STRETCH_NONE:
    offset_x =
      (wp_align == WP_LEFT) ? 0 :
      (wp_align == WP_CENTER) ? (win_width - bm_width) / 2 :
      (wp_align == WP_RIGHT) ? win_width - bm_width : 0;
    offset_y =
      (wp_valign == WP_TOP) ? 0 :
      (wp_valign == WP_MIDDLE) ? (win_height - bm_height) / 2 :
      (wp_valign == WP_BOTTOM) ? win_height - bm_height : 0;
    if (wp_position == WP_TILE) {
      int m = offset_x % bm_width;
      int n = offset_y % bm_height;
      int y = n ? n - bm_height : 0;
      for (; y <= win_height - n; y += bm_height) {
        int x = m ? m - bm_width : 0;
        for (; x <= win_width - m; x += bm_width) {
          brt->DrawBitmap(d2dBM,
                          D2D1::RectF((FLOAT) x,
                                      (FLOAT) y,
                                      (FLOAT) x + bm_width,
                                      (FLOAT) y + bm_height),
                          1.0f, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
        }
      }
    } else {
      brt->DrawBitmap(d2dBM,
                      D2D1::RectF((FLOAT) offset_x,
                                  (FLOAT) offset_y,
                                  (FLOAT) offset_x + bm_width,
                                  (FLOAT) offset_y + bm_height),
                      1.0f, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
    }
    break;
  case STRETCH_WIDTH:
    stretch_width = win_width;
    stretch_height = bm_height * win_width / bm_width;;
    offset_x = 0;
    offset_y =
      (wp_valign == WP_TOP) ? 0 :
      (wp_valign == WP_MIDDLE) ? (win_height - stretch_height) / 2 :
      (wp_valign == WP_BOTTOM) ? win_height - stretch_height : 0;
    brt->DrawBitmap(d2dBM,
                    D2D1::RectF((FLOAT) offset_x,
                                (FLOAT) offset_y,
                                (FLOAT) offset_x + stretch_width,
                                (FLOAT) offset_y + stretch_height),
                    1.0f, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
    break;
  case STRETCH_HEIGHT:
    stretch_width = bm_width * win_height / bm_height;;
    stretch_height = win_height;
    offset_x =
      (wp_align == WP_LEFT) ? 0 :
      (wp_align == WP_CENTER) ? (win_width - stretch_width) / 2 :
      (wp_align == WP_RIGHT) ? win_width - stretch_width : 0;
    offset_y = 0;
    brt->DrawBitmap(d2dBM,
                    D2D1::RectF((FLOAT) offset_x,
                                (FLOAT) offset_y,
                                (FLOAT) offset_x + stretch_width,
                                (FLOAT) offset_y + stretch_height),
                    1.0f, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
    break;
  case STRETCH_BOTH:
    brt->DrawBitmap(d2dBM,
                    D2D1::RectF((FLOAT) 0,
                                (FLOAT) 0,
                                (FLOAT) 0 + win_width,
                                (FLOAT) 0 + win_height),
                    1.0f,
                    D2D1_BITMAP_INTERPOLATION_MODE_LINEAR,
                    D2D1::RectF((FLOAT) 0,
                                (FLOAT) 0,
                                (FLOAT) 0 + bm_width, (FLOAT) 0 + bm_height));
    break;
  }

  brt->EndDraw();
  brt->GetBitmap(&wp);
  brt->CreateBitmapBrush(wp, &d2dBB);

  wp->Release();
  brt->Release();

  return;
}

static void wp_release()
{
  if (d2dBB) {
    d2dBB->Release();
    d2dBB = NULL;
  }
}

static void wp_draw(const D2D1_RECT_F * rect)
{
  if (!d2dRT) {
    return;
  }

  if (bg_wallpaper == BG_NONE) {
    d2dSCBbg->SetColor(D2D1::ColorF(colours[258],
                                    alphas[ALPHA_DEFAULT_BG][bg_active]));
    if ((bg_effect == BG_GLASS) && (border_style == BS_ROUNDED)) {
      FLOAT w = (FLOAT) window_border;
      D2D1_ROUNDED_RECT rrect = { *rect, w, w };
      d2dRT->FillRoundedRectangle(rrect, d2dSCBbg);
    } else {
      d2dRT->FillRectangle(rect, d2dSCBbg);
    }
    return;
  }

  if (!d2dBB) {
    return;
  }

  d2dBB->SetOpacity(alphas[ALPHA_DEFAULT_BG][bg_active]);

  if (bg_wallpaper == BG_FILE_DESKTOP) {
    POINT po;
    po.x = (LONG) rect->left;
    po.y = (LONG) rect->top;
    ClientToScreen(hwnd, &po);
    d2dBB->SetTransform(D2D1::Matrix3x2F::Translation(-(FLOAT) po.x,
                                                      -(FLOAT) po.y));
  }

  if ((bg_wallpaper == BG_FILE) || (bg_wallpaper == BG_FILE_DESKTOP)) {
    if ((bg_effect == BG_GLASS) && (border_style == BS_ROUNDED)) {
      FLOAT w = (FLOAT) window_border;
      D2D1_ROUNDED_RECT rrect = { *rect, w, w };
      d2dRT->FillRoundedRectangle(rrect, d2dBB);
    } else {
      d2dRT->FillRectangle(rect, d2dBB);
    }
    return;
  }

  if (bg_wallpaper == BG_FILE_DESKTOP) {
    d2dBB->SetTransform(D2D1::Matrix3x2F::Identity());
  }

  if (bg_wallpaper == BG_DESKTOP) {
  }
  return;
}


static void bg_resize(int draw)
{
  if (draw) {
    bg_glass();
    wp_create();
  }
}


static void bg_move(int draw)
{
  if ((draw || wp_moving) &&
      ((bg_wallpaper == BG_FILE_DESKTOP) ||
       (bg_wallpaper == BG_DESKTOP))) {
    term_update(term);
  }
}


static void bg_glass()
{
  BOOL b = FALSE;
  DwmIsCompositionEnabled(&b);
  if (!b) {
    return;
  }

  // Windows 10
  if (osVersion.dwMajorVersion > 9) {
    if (bg_effect == BG_PLANE) {
      return;
    }
    if (!p_SetWindowCompositionAttribute) {
      HMODULE hmLib = NULL;
      hmLib = load_system32_dll("user32.dll");
      if (hmLib) {
        GET_WINDOWS_FUNCTION(hmLib, SetWindowCompositionAttribute);
      }
    }
    AccentPolicy policy = {3, 0, 0, 0};
    WINCOMPATTRDATA data = {19, &policy, sizeof(policy)};
    p_SetWindowCompositionAttribute(hwnd, &data);
    return;
  }

  // Windows Vista, 7
  RECT rc;
  GetClientRect(hwnd, &rc);

  HRGN hrgn;
  if (bg_effect == BG_PLANE) {
    hrgn = CreateRectRgn(-1, -1, 1, 1);
  } else {
    hrgn = CreateRectRgn(rc.left, rc.top,
                         rc.right - rc.left, rc.bottom - rc.top);
  }
  DWM_BLURBEHIND bb = { 0 };
  bb.dwFlags = DWM_BB_ENABLE | DWM_BB_BLURREGION;
  bb.fEnable = TRUE;
  bb.hRgnBlur = hrgn;
  DwmEnableBlurBehindWindow(hwnd, &bb);

  MARGINS margins = { 0 };
  if ((border_style != BS_NORMAL) && (bg_effect != BG_PLANE)) {
    margins.cxLeftWidth = -1;
  }
  DwmExtendFrameIntoClientArea(hwnd, &margins);
}
