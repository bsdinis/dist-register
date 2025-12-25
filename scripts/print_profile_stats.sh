#!/usr/bin/env bash

set -e

function usage {
    echo "$0 [-h|--help] [-v|--verbose] [--kv|-k \"<key>:<value>\"]* <file>"
}
options=$(getopt -l "help,verbose,kv:" -o "hvk:" -a -- "$@")

eval set -- "$options"

KV_PAIRS=()
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
        -k|--kv)
            KV_PAIRS+=("$2")
            shift # shift value too
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

verus_profile=$(jq -r '."verus"."profile"' < ${FILENAME})
verus_version=$(jq -r '."verus"."version"' < ${FILENAME})
verus_platform_os=$(jq -r '."verus"."platform"."os"' < ${FILENAME})
verus_arch=$(jq -r '."verus"."platform"."arch"' < ${FILENAME})
verus_platform="${verus_platform_os}_${verus_arch}"
rust_toolchain=$(jq -r '."verus"."toolchain"' < ${FILENAME})
verus_commit=$(jq -r '."verus"."commit"' < ${FILENAME})
num_threads=$(jq '."times-ms"."num-threads"' < ${FILENAME})
total_ms=$(jq '."times-ms"."total"' < ${FILENAME})
cpu_time_ms=$(jq '."times-ms"."estimated-cpu-time"' < ${FILENAME})
verification_wall_clock_ms=$(jq '."times-ms"."verification"."total"' < ${FILENAME})
verification_cpu_ms=$(jq '."times-ms"."total-verify"' < ${FILENAME})
smt_run_ms=$(jq '."times-ms"."smt"."smt-run"' < ${FILENAME})
sorted_modules=$(jq \
    '."times-ms"."total-verify-module-times"' \
    < ${FILENAME} \
    | jq 'sort_by(.time)' \
)

printf "| %35s | %37s    |\n" "" ""
printf "|---|---|\n"
printf "| %35s | %37s    |\n" "profile" ${verus_profile}
printf "| %35s | %37s    |\n" "version" ${verus_version}
printf "| %35s | %37s    |\n" "platform" ${verus_platform}
printf "| %35s | %37s    |\n" "toolchain" ${rust_toolchain}
printf "| %35s | %39s |\n" "verus commit" ${verus_commit}
printf "| %35s | %37s    |\n" "hostname" "$(hostname)"
printf "| %35s | %37s    |\n" "n_threads" ${num_threads}
printf "| %35s | %37s ms |\n" "total (wall-clock)" ${total_ms}
printf "| %35s | %37s ms |\n" "total (cpu)" ${cpu_time_ms}
printf "| %35s | %37s ms |\n" "verification (wall-clock)" ${verification_wall_clock_ms}
printf "| %35s | %37s ms |\n" "verification (cpu)" ${verification_cpu_ms}
printf "| %35s | %37s ms |\n" "smt run (cpu)" ${smt_run_ms}

for n in {1..5};
do
    module=$(echo $sorted_modules | jq ".[-$n]")
    name=$(echo $module | jq -r '."module"')
    time=$(echo $module | jq '."time"')
    printf "| %35s | %37s ms |\n" "${name}" "${time}"
done


for kv in "${KV_PAIRS[@]}";
do
    k=$(echo $kv | cut -d'|' -f 1)
    v=$(echo $kv | cut -d'|' -f 2)
    printf "| %35s | %37s    |\n" "${k}" "${v}"
done

popd >/dev/null
