define([gitversion], esyscmd([sh -c "git log --oneline | wc -l | tr -d ' \n'"]))

AC_INIT([lustrec], 1.7, [ploc@garoche.net])
AC_SUBST(VERSION_NUMBER, 1.7)
AC_SUBST(VERSION_CODENAME, "Xia/Huai")

gitbranch=`git branch | grep \* | sed "s/\*[ ]*//"`
AC_SUBST(GITBRANCH, "$gitbranch")
if test x"$GITBRANCH" != "xmaster"; then
  AC_SUBST(CDASHSUBPROJ, "unstable")
else
  AC_SUBST(CDASHSUBPROJ, "master")
fi

# Next release will be
#AC_INIT([lustrec], [1.8], [ploc@garoche.net])
#AC_SUBST(VERSION_CODENAME, "Xia/Mang")
AC_MSG_NOTICE(Git branch: ${GITBRANCH})
AC_CONFIG_SRCDIR([src/main_lustre_compiler.ml])
AC_CONFIG_SRCDIR([src/main_lustre_testgen.ml])

AC_PATH_PROG([OCAMLC],[ocamlc],[:])
AC_MSG_CHECKING(OCaml version)
ocamlc_version=`$OCAMLC -v | grep version | rev| cut -d \  -f 1 | rev`
major=`echo $ocamlc_version | cut -d . -f 1`
minor=`echo $ocamlc_version | cut -d . -f 2`
if (test "$major" -lt 3 -a "$minor" -lt 11 ); then
  AC_MSG_ERROR([Ocaml version must be at least 3.11. You have version $ocamlc_version])
fi
AC_MSG_RESULT(valid ocaml version detected: $ocamlc_version)

AC_PATH_PROG([OCAMLBUILD],[ocamlbuild],[:])

# Handle a mismatch in available function btw 4.02 and 4.04
if (test $"$major" -eq 4 -a "$minor" -gt 2); then
   AC_SUBST(UPPERCASEFUN, "String.uppercase_ascii")
else
   AC_SUBST(UPPERCASEFUN, "String.uppercase")
fi

# default prefix is /usr/local
AC_PREFIX_DEFAULT(/usr/local)

dnl AC_ARG_WITH([ocamlgraph-path],
dnl         [AS_HELP_STRING([--ocamlgraph-path],
dnl               [specify the path of ocamlgraph library. graph.cmxa should be in ocamlgraph-path @<:@default=$(ocamlfind query ocamlgraph)@:>@])],
dnl         [AS_IF([test "x$ocamlgraph_path" = xno],
dnl                 [AC_MSG_ERROR([ocamlgraph library is needed])],
dnl                 [test "x$ocamlgraph_path" = xyes],
dnl                 [OCAMLGRAPH_PATH=$(ocamlfind query ocamlgraph)],
dnl                 [OCAMLGRAPH_PATH=$ocamlgraph_path]
dnl         )],
dnl         [OCAMLGRAPH_PATH=$(ocamlfind query ocamlgraph)]
dnl )
dnl AC_SUBST(OCAMLGRAPH_PATH)


# Checking libs
AC_CHECK_PROG(FINDLIB_CHECK,ocamlfind,yes)
if test x"$FINDLIB_CHECK" != x"yes" ; then
   AC_MSG_ERROR(ocamlfind required!)
fi
dnl AC_MSG_RESULT(Hourrah: ocamlfind found!)

# Checks for libraries.
# OCamlgraph
AC_MSG_CHECKING(ocaml libraries required (ocamlgraph cmdliner fmt logs num)) 
AS_IF([ocamlfind query ocamlgraph cmdliner fmt logs num >/dev/null 2>&1],
    [],[AC_MSG_ERROR(A few ocaml library required. opam install ocamlgraph cmdliner fmt logs num should solve the issue)],
)
AC_MSG_RESULT(yes)

#Yojson
AC_MSG_CHECKING(yojson library (optional))
AS_IF([ocamlfind query yojson >/dev/null 2>&1],
    [yojson=yes; AC_MSG_RESULT(yes)],[yojson=no; AC_MSG_WARN(Yojson required for lustresf. opam install yojson should solve the issue)],
)

# Seal
AC_MSG_CHECKING(seal library (optional))
AS_IF([ocamlfind query seal >/dev/null 2>&1],
    [seal=yes; AC_MSG_RESULT(yes)],[seal=no; AC_MSG_RESULT(no)],
)
AS_IF([test "x$seal" = "xyes"], [
   AC_SUBST(LUSTREV_SEAL, "(module Seal_verifier.Verifier : VerifierType.S);")
   AC_SUBST(LUSTREV_SEAL_TAG, "<**/*verifier.native>: package(seal)")
])

# Tiny
AC_MSG_CHECKING(tiny library (optional))

AC_ARG_ENABLE(tiny, [AS_HELP_STRING([--disable-tiny],
              [disable Tiny dependencies. Enabled by default if available.])])

AS_IF([ocamlfind query tiny >/dev/null 2>&1],
    [tiny=yes; AC_MSG_RESULT(yes)],[tiny=no; AC_MSG_RESULT(no)],
)

AS_IF([test "x$enable_tiny" != "xno"], [
  if (test "x$tiny" = xyes ); then
   dnl   AC_SUBST(LUSTREV_TINY_TAG, "<**/*>: package(apron.boxMPQ), package(apron.octMPQ), package(apron.polkaMPQ), package(tiny)")
   AC_SUBST(LUSTREV_TINY, "(module Tiny_verifier.Verifier : VerifierType.S);")
   AC_SUBST(LUSTREV_TINY_TAG, ["<**/*>: package(apron.boxMPQ), package(apron.octMPQ), package(apron.polkaMPQ), package(tiny)"])
  fi
])

# z3 (optional)

AC_ARG_ENABLE(z3, [AS_HELP_STRING([--disable-z3],
              [disable Z3 dependencies. Enabled by default if available.])])
	
AC_MSG_CHECKING(z3 library)


#define([z3path], esyscmd([ocamlfind query z3 | tr -d '\n']))
#define([z3path], esyscmd([opam config var Z3:lib | tr -d '\n']))

AS_IF([ocamlfind query z3 >/dev/null 2>&1],
    [z3=yes; AC_MSG_RESULT([yes])],[zustre=no; AC_MSG_RESULT(no)],
)

AS_IF([test "x$enable_z3" != "xno"], [
  if (test "x$z3" = xyes ); then
   define([z3path], esyscmd([ocamlfind query z3 | tr -d '\n']))
   AC_SUBST(LUSTREV_ZUSTRE, "(module Zustre_verifier.Verifier : VerifierType.S);")
   AC_SUBST(LUSTREV_Z3_TAG, "<**/*verifier.native> or <tools/zustre/*.ml> or <tools/zustre/*.mli> or <tools/seal/seal_extract.ml> or <tools/seal/seal_extract.mli>: package(z3)")
   AC_SUBST(Z3LIBPATH, "z3path")
  fi
])



# Salsa
AC_ARG_ENABLE(salsa, [AS_HELP_STRING([--disable-salsa],
              [disable Salsa plugin. Enabled by default if available.])])

AC_MSG_CHECKING(salsa library)
AS_IF([ocamlfind query salsa >/dev/null 2>&1],
    [salsa=yes; AC_MSG_RESULT(yes)],[salsa=no; AC_MSG_WARN(no)]
)


AS_IF([test "x$enable_salsa" != "xno"], [
  if (test "x$salsa" = xyes ); then
   AC_SUBST(SALSA, "(module Salsa_plugin.Plugin : PluginType.S);")
   AC_SUBST(SALSA_TAG, "<**/*.native> or <plugins/salsa/*.cm?> : package(salsa)")
  fi
])

# GMP
AC_CHECK_LIB(gmp, __gmpz_init,
      [gmp=yes],
      [AC_MSG_RESULT([GNU MP not found])
      gmp=no])

AC_CHECK_LIB(mpfr, mpfr_add, [mpfr=yes],
		   [AC_MSG_RESULT(
[MPFR not found])
mpfr=no])

# lustresf
AC_ARG_ENABLE(lustresf, [AS_HELP_STRING([--disable-lustresf],
              [disable lustresf compilation. Enabled by default.])])

AC_SUBST_FILE(lustresf)
AC_SUBST_FILE(lustresf_src)
lustresf=/dev/null
lustresf_src=/dev/null

AS_IF([test "x$enable_lustresf" != "xno"], [
  AC_MSG_CHECKING(yojson library for lustresf)
  AS_IF([ocamlfind query yojson >/dev/null 2>&1],
      [yojson=yes; AC_MSG_RESULT(yes)],[yojson=no; AC_MSG_ERROR(Yojson required for lustresf. opam install yojson should solve the issue)],
  )
  lustresf=Makefile-lustresf.in
  lustresf_src=src/Makefile-lustresf.in
  AC_SUBST(lustresf_target, "lustresf")
])

# Checking availability of path to regression tests
tests_path="../lustrec-tests/regression_tests"

AC_ARG_WITH([tests-path],
            [AS_HELP_STRING([--with-tests-path],
               [provides path to test suite (default is ../lustrec-test if available)])],
            [tests_path="$withval";
	     if (test "x$tests_path" = xyes); then
	       AC_MSG_ERROR(Option --with-tests-path requires a parameter: eg. --with-tests-path=value);
	     fi],
            )
AC_MSG_NOTICE($tests_path)
AC_CHECK_FILE(${tests_path}/CMakeLists.txt,
              [
	      valid_test_path=true
	      ],
	      [
	      valid_test_path=false
	        AC_SUBST(PATH_TO_TESTS, $tests_path)	      ])
AC_SUBST(PATH_TO_TESTS_DEFINED, $valid_test_path)
AC_SUBST(PATH_TO_TESTS, $tests_path)

# End of config

AC_DEFUN([AC_DEFINE_DIR], [
  prefix_NONE=
  exec_prefix_NONE=
  test "x$prefix" = xNONE && prefix_NONE=yes && prefix=$ac_default_prefix
  test "x$exec_prefix" = xNONE && exec_prefix_NONE=yes && exec_prefix=$prefix
dnl In Autoconf 2.60, ${datadir} refers to ${datarootdir}, which in turn
dnl refers to ${prefix}.  Thus we have to use `eval' twice.
  eval ac_define_dir="\"[$]$2\""
  eval ac_define_dir="\"$ac_define_dir\""
  AC_SUBST($1, "$ac_define_dir")
  AC_DEFINE_UNQUOTED($1, "$ac_define_dir", [$3])
  test "$prefix_NONE" && prefix=NONE
  test "$exec_prefix_NONE" && exec_prefix=NONE
])

AC_DEFINE_DIR([abs_datadir], [datadir])

# Instanciation
AC_CONFIG_FILES([opam
		 Makefile
		 src/Makefile
		 src/version.ml
		 src/pluginList.ml
		 src/verifierList.ml
		 src/_tags
		 src/ocaml_utils.ml
		 include/z3librc
		 share/FindLustre.cmake
		 ])

AC_OUTPUT


# summary
AC_MSG_NOTICE(******** Configuration ********)
AC_MSG_NOTICE(bin path:     $prefix/bin)
AC_MSG_NOTICE(include path: $prefix/include)
AC_MSG_NOTICE(********    Plugins    ********)

  if (test "x$gmp" = xyes -a "x$mpfr" = xyes ); then
      AC_MSG_NOTICE([MPFR option enabled])
  else
      AC_MSG_WARN([MPFR option cannot be activated. Requires GMP and MPFR libs])
  fi

  if (test "x$salsa" = xyes -a "x$enable_salsa" != xno); then
      AC_MSG_NOTICE([Salsa plugin enabled])
  else
      AC_MSG_NOTICE([Salsa plugin disabled])
  fi

  if (test "x$z3" = xyes -a "x$enable_z3" != xno); then
      AC_MSG_NOTICE([Z3 dependencies enabled])
  else
      AC_MSG_NOTICE([Z3 dependencies disabled])
  fi

  if (test "x$yojson" = xyes -a "x$enable_lustresf" != "xno"); then
      AC_MSG_NOTICE([lustresf available])
  else
      if (test "x$enable_lustresf" = "xno"); then
        AC_MSG_NOTICE([lustresf not available (you explicitely disabled it)])
      else
        AC_MSG_NOTICE([lustresf not available])
      fi
  fi
AC_MSG_NOTICE(********   Verifiers    ********)

  if (test "x$z3" = xyes  -a "x$enable_z3" != xno); then
      AC_MSG_NOTICE([Zustre enabled])
      AC_MSG_WARN(Z3 shared lib (libz3.so) has to be available in the LD_LIBRARY_PATH (DYLD_LIBRARY_PATH in OSX).)
      dnl AC_MSG_WARN(It is currently located in "z3path")
      AC_MSG_WARN(If not already available run "source ${prefix}/include/lustrec/z3librc")
      AC_MSG_WARN(or add that line to your ~/.profile or ~/.bashrc)
else
      AC_MSG_NOTICE([Zustre disabled. Require Z3 ocaml library])
  fi

if (test "x$seal" = "xyes" -a "x$z3" = xyes  -a "x$enable_z3" != xno); then
      AC_MSG_NOTICE([Seal   enabled])
  else
      AC_MSG_NOTICE([Seal   disabled. Require Z3 library])
  fi


  if (test "x$tiny" = xyes  -a "x$enable_tiny" != xno); then
      AC_MSG_NOTICE([Tiny   enabled])
  else
      AC_MSG_NOTICE([Tiny   disabled.])
  fi

AC_MSG_NOTICE(****** Regression Tests  ******)
if (test "x$valid_test_path" = xfalse); then
  AC_MSG_NOTICE(no valid tests path provided ($tests_path))
else
AC_MSG_NOTICE(tests path: $tests_path)
fi
AC_MSG_NOTICE(******** Configuration ********)
AC_MSG_NOTICE(Execute "make; make install" now)
