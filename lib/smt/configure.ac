dnl Process this file with autoconf to produce a configure script. -*-Autoconf-*-
dnl
dnl %CopyrightBegin%
dnl
dnl Copyright Ericsson AB 2018-2023. All Rights Reserved.
dnl
dnl Licensed under the Apache License, Version 2.0 (the "License");
dnl you may not use this file except in compliance with the License.
dnl You may obtain a copy of the License at
dnl
dnl     http://www.apache.org/licenses/LICENSE-2.0
dnl
dnl Unless required by applicable law or agreed to in writing, software
dnl distributed under the License is distributed on an "AS IS" BASIS,
dnl WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
dnl See the License for the specific language governing permissions and
dnl limitations under the License.
dnl
dnl %CopyrightEnd%
dnl

dnl define([AC_CACHE_LOAD], )dnl
dnl define([AC_CACHE_SAVE], )dnl

AC_INIT
AC_CONFIG_SRCDIR([vsn.mk])
AC_PREREQ([2.71])

m4_include([otp.m4])

AC_CONFIG_AUX_DIR([${ERL_TOP}/make/autoconf])

ERL_CANONICAL_SYSTEM_TYPE

AC_LANG(C)

LM_PRECIOUS_VARS

## Delete previous failed configure results
if test -f ./CONF_INFO; then
   rm ./CONF_INFO
fi

if test "$cross_compiling" = "yes"; then
    CROSS_COMPILING=yes
else
    CROSS_COMPILING=no
fi
AC_SUBST(CROSS_COMPILING)

ERL_XCOMP_SYSROOT_INIT

AC_PROG_CC
AC_PROG_CXX
LM_WINDOWS_ENVIRONMENT

AC_LANG_PUSH(C++)
CXXFLAGS="$CXXFLAGS -std=c++17"
AC_COMPILE_IFELSE(
    [AC_LANG_PROGRAM([[]],
     [[#if __cplusplus < 201703L
      #error "Needs C++17 compiler"
      #endif]])],
    [AC_MSG_CHECKING([for C++17 support])
     AC_MSG_RESULT([yes])
     HAVE_CXX17=true],
    [AC_MSG_CHECKING([for C++17 support])
     AC_MSG_RESULT([no])
     HAVE_CXX17=false])
AC_LANG_POP()

AS_IF([test "$CXX" = false -o "$HAVE_CXX17" = false],
      [AC_MSG_ERROR([z3_nif needs a C++ compiler with C++17 support])])

AS_CASE([$host_os],
    [win32], [],
    [
        Z3_CFLAGS=`pkg-config --silence-errors --cflags z3`
        Z3_LIBS=`pkg-config --silence-errors --libs z3`
    ]
)

ERL_DED

AC_SUBST(Z3_CFLAGS)
AC_SUBST(Z3_LIBS)

AC_CONFIG_FILES([c_src/$host/Makefile:c_src/Makefile.in])
AC_OUTPUT
