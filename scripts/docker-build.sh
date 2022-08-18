#!/bin/sh

set -e -u

usage () {
	cat <<EOF
Usage: $_SCRIPTNAME
         [-h]
         AGDA_VERSION AGDA_STDLIB_VERSION ARCHIVE
         [DOCKER_OPTIONS]

Options:
  -h  Show this message
EOF
}

usage_and_exit_zero () {
	usage
	exit 0
}

usage_and_exit_nonzero () {
	usage
	exit 2
}

clean_and_exit () {
	[ -z "${_BUILD_CONTEXT_PATH:+x}" ] || [ ! -e "$_BUILD_CONTEXT_PATH" ] || rm -r $_BUILD_CONTEXT_PATH
	exit $_EXITCODE
}

_SCRIPTNAME=$(basename $0)
_SCRIPTDIR=$(dirname $0)

DOCKERFILE_NAME=Dockerfile
_DOCKERFILE_PATH=$_SCRIPTDIR/$DOCKERFILE_NAME
[ -f "$_DOCKERFILE_PATH" ] || { echo "File \`$DOCKERFILE_NAME' not found in $_SCRIPTDIR... Abort."; exit 1; }

QUIET=
while getopts h name
do
	case $name in
	h) usage_and_exit_zero;;
	?) usage_and_exit_nonzero;;
	esac
done
shift $(($OPTIND - 1))

[ $# -lt 3 ] && usage_and_exit_nonzero

AGDA_VERSION=$1
AGDA_STDLIB_VERSION=$2
PROJECT_ARCHIVE_SRC_PATH=$3
shift 3

[ -f "$PROJECT_ARCHIVE_SRC_PATH" ] || { echo "Input file \`$PROJECT_ARCHIVE_SRC_PATH' does not exist... Abort."; exit 1; }

trap '_EXITCODE=$?; trap - INT QUIT TERM EXIT; clean_and_exit' INT QUIT TERM EXIT

_BUILD_CONTEXT_PATH=$(mktemp -d --tmpdir ${_SCRIPTNAME}_build_context.XXXXXXXXXX)
(umask 022 && cp --no-preserve=mode $_DOCKERFILE_PATH $PROJECT_ARCHIVE_SRC_PATH $_BUILD_CONTEXT_PATH/)
DOCKER_BUILDKIT=1 docker build \
	-f $_BUILD_CONTEXT_PATH/$DOCKERFILE_NAME \
	--build-arg AGDA_VERSION=$AGDA_VERSION \
	--build-arg AGDA_STDLIB_VERSION=$AGDA_STDLIB_VERSION \
	--build-arg PROJECT_ARCHIVE_SRC_RELPATH=$(basename $PROJECT_ARCHIVE_SRC_PATH) \
	$@ \
	$_BUILD_CONTEXT_PATH
