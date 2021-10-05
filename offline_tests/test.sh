#!/usr/bin/env bash

bold="\033[1m"
red="\033[31m"
green="\033[32m"
normal="\033[0m"

LUSTREC=$1
LUS_FILES=$2

PROVERS=alt-ergo,z3,cvc4
TIMEOUT="${TIMEOUT:-30}"
JOBS="${JOBS:-16}"
FRAMA_C_ARGS="-wp -wp-model ref,real -wp-prover $PROVERS -wp-run-all-provers\
    -wp-timeout $TIMEOUT -wp-par $JOBS"
FRAMA_C=frama-c

# max length of file names
S=0
for f in $LUS_FILES
do
    if [ "${#f}" -gt "$S" ]; then
        S=${#f}
    fi
done

compile() {
    printf "${bold}Compilation tests:${normal}\n"
    N=0
    OK=0
    KO=0
    for f in $LUS_FILES
    do
        printf "${normal}%-${S}s" "$f"
        N=$(( N + 1 ))
        if $LUSTREC -acsl-spec "$f" >/dev/null 2>/tmp/err; then
            OK=$(( OK + 1 ))
            CHECK="${green}OK${normal}"
        else
            KO=$(( KO + 1 ))
            ERR=$(</tmp/err)
            CHECK="${red}KO\n  $ERR\n${normal}"
        fi
        printf " %b\n" "${CHECK}"
    done
    printf "\n${normal}OK: ${green}%d${normal} (${red}%d${normal}) / %d\n\n"\
        "${OK}" "${KO}" "${N}"
}

verif() {
    printf "${bold}Verification tests:${normal}\n"
    N=0
    OK=0
    KO=0
    for f in *.c
    do
        printf "${normal}%-${S}s" "$f"
        if $FRAMA_C $FRAMA_C_ARGS "$f" > /tmp/log; then
            sed -n '/Proved goals/{N;N;N;N;p;q}' /tmp/log > "$f".log
            OK=$(( OK + 1 ))
            LOG=$(<"$f".log)
            CHECK="${green}OK\n  $LOG\n${normal}"
        else
            KO=$(( KO + 1 ))
            ERR=$(</tmp/log)
            CHECK="${red}KO\n  $ERR\n${normal}"
        fi
        printf " %b\n" "${CHECK}"
    done
    printf "\n${normal}OK: ${green}%d${normal} (${red}%d${normal}) / %d\n\n"\
        "${OK}" "${KO}" "${N}"
}

compile

verif
