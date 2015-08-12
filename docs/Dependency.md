
## OCaml

+ Ubuntu

    ```
    apt-get install ocaml ocaml-nox ocaml-native-compilers ocaml-doc ocaml-findlib oasis libpcre-ocaml-dev
    ```

+ Fedora

    ```
    yum install ocaml ocaml-foo-devel ocaml-camlp4-devel ocaml-ocamldoc ocaml-findlib-devel ocaml-extlib-devel ocaml-calendar-devel
    ```

## OPAM

+ Ubuntu

    ```
    apt-get install opam
    ```

+ Fedora

    先下载[RPM包](http://software.opensuse.org/download.html?project=home%3Aocaml&package=opam)，然后使用rpm安装
    
    ```
    rpm -ivh opam.rpm
    ```

使用普通用户（非ROOT用户）进行配置

```
opam init
opam switch 4.01.0
eval `opam config env`
```

## UTOP

```
opam install utop
```

## Core

```
opam install core
opam install async yojson core_extended core_bench cohttp async_graphics cryptokit menhir
```

然后编辑文件`~/.ocamlinit`，添加内容

```
#use "topfind";;
#thread;;
#camlp4o;;
#require "core.top";;
#require "core.syntax";;
#require “async”;;
```

## z3

```
git clone git@github.com:Z3Prover/z3.git
python scripts/mk_make.py
cd build
make
sudo make install
```

## pexpect

```
pip install pexpect
```