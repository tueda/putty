This is a customized version of PuTTY, compilable on Cygwin 2.5.1
(MinGW 64-bit). It contains sources from

- [PuTTY](http://www.chiark.greenend.org.uk/~sgtatham/putty/) (by Simon Tatham)
- [PuTTYjp](http://hp.vector.co.jp/authors/VA024651/PuTTYkj.html) (by Hideki EIRAKU)
- [PuTTY ごった煮版](http://yebisuya.dip.jp/Software/PuTTY/) (by  蛭子屋 双六)
- [reconnect patch](http://www.warp13.co.uk/putty.py) (by warp13)
- [D2D/DW PuTTY](http://ice.hotmint.com/putty/d2ddw.html) (by Nag)

Build
-----

```
git clone --depth=1 https://github.com/tueda/putty.git
cd putty
./mkfiles.pl
cd windows
make -f Makefile.cyg TOOLPATH=x86_64-w64-mingw32-
```

Syncing the fork
----------------

```
git clone https://github.com/tueda/putty.git
cd putty
git remote add upstream git://git.tartarus.org/simon/putty.git
git fetch upstream
```

--------

The original README file is [here](README).
