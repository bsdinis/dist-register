#!/usr/bin/env bash

set -e

function usage {
    echo "$0 [-h|--help] [-v|--verbose] <file>"
}
options=$(getopt -l "help,verbose" -o "hv" -a -- "$@")

eval set -- "$options"

status=0
while true
do
    case "$1" in
        -h|--help)
            usage
            exit $status
            ;;
        -v|--verbose)
            set -x
            ;;
        --)
            shift
            break
            ;;
    esac
    shift
done

FILENAME=$1
if [ -z "$FILENAME" ];
then
    usage
    exit 1
elif ! [ -r "${FILENAME}" ];
then
    echo "file not found: ${FILENAME}"
    exit 1
fi

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")
PROJECT_ROOT=$(dirname ${SCRIPT_DIR})

pushd ${PROJECT_ROOT} >/dev/null

jq \
    '."times-ms"."total-verify-module-times"' \
    < ${FILENAME} \
    | jq 'sort_by(.time)'

popd >/dev/null
