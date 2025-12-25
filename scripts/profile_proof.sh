#!/usr/bin/env bash

set -e

function usage {
    echo "$0 [-h|--help] [-v|--verbose] [-s|--skip-logging] <file>"
}
options=$(getopt -l "help,verbose,skip-logging" -o "hvs" -a -- "$@")

eval set -- "$options"

LOG=1
status=0
while true
do
    case "$1" in
        -h|--help)
            usage
            exit $status
            ;;
        -s|--skip-logging)
            LOG=0
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

SCRIPT_DIR=$(dirname "$(readlink -f "$0")")
PROJECT_ROOT=$(dirname ${SCRIPT_DIR})

function get_log_id() {
    local ls_output
    ls_output=$(ls ${PROJECT_ROOT}/timing_tracker/*.json)
    local awk_input="0000"
    for file in ${ls_output};
    do
        local b
        b=$(basename ${file} | cut -d_ -f1)
        awk_input="${awk_input}\n${b}"
    done

    awk -F'\n' 'BEGIN { max = 0}; { if ($0 > max) { max = $0 } }; END { printf "%04d\n", max+1 }' <(echo -e ${awk_input})
}

pushd ${PROJECT_ROOT}

log_id=$(get_log_id)
log_name="${log_id}_$(date +'%Y_%m_%d_%H_%M_%S')".json
log_filename="timing_tracker/${log_name}"

if [ ${LOG} -eq 1 ];
then
    cargo verus verify -- \
        --triggers-mode silent \
        --time-expanded \
        --output-json > ${log_filename}
else
    cargo verus verify -- \
        --triggers-mode silent \
        --time-expanded
fi

ELAPSED_TIME='Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): '
ELAPSED_AWK_PROGRAM="/${ELAPSED_TIME}/ { print \$2 }"
time_reported=$(/usr/bin/time -v cargo verus verify -- --triggers-mode silent 2>&1 >/dev/null | tee /dev/stderr | awk -F': ' "${ELAPSED_AWK_PROGRAM}")

if [ -r ${log_filename} ];
then
    ${SCRIPT_DIR}/print_profile_stats.sh --kv "elapsed wall clock|${time_reported}" ${log_filename}
fi

popd
