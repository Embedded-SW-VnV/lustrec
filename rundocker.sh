#!/usr/bin/env bash

containerId=leliobrun/lustrec-env

command -v docker >/dev/null 2>&1 || { \
        echo >&2 "docker is required but could not be found.  Aborting."; \
        echo >&2 "To setup Docker: https://docs.docker.com/engine/getstarted/step_one/"; \
        exit 1; }

docker run -it --rm --user $(id -u):$(id -g)\
    -v $PWD:/home/opam/lustrec $containerId $1
