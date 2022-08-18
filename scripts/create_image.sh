#!/bin/sh

set -e -u

QEMU_IMAGE_SIZE=16G

usage () {
	cat <<EOF
Usage: $_SCRIPTNAME
         [-h] [-a ARCHIVE] [-f FILE] [-o] [-q] [-t NAME]
         AGDA_VERSION AGDA_STDLIB_VERSION

Options:
  -h          Show this message
  -a ARCHIVE  Extract files from ARCHIVE to the user home directory
              in the intermediate Docker image
              (default: $PROJECT_ARCHIVE_SRC_PATH)
  -f FILE     Create disk image FILE (default: $QEMU_IMAGE_PATH)
  -o          Overwrite FILE if it exists
  -q          Suppress Docker build output
  -t NAME     Keep the intermediate Docker image as NAME
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
	[ -z "${_DOCKER_IMAGE_NAME:+x}" ] || [ -n "$NEW_DOCKER_IMAGE_NAME" ] || ! docker inspect $_DOCKER_IMAGE_NAME >/dev/null 2>&1 || docker image rm $_DOCKER_IMAGE_NAME >/dev/null
	exit $_EXITCODE
}

random_string () {
	ARRAY=$1
	CHARS=$2
	tr -dc $ARRAY </dev/urandom | head -c $CHARS
}

_SCRIPTNAME=$(basename $0)
_SCRIPTDIR=$(dirname $0)

CONVERT_DEBIAN_DOCKER_TO_QEMU_NAME=convert_debian_docker_to_qemu.sh
DOCKER_BUILD_NAME=docker-build.sh

_CONVERT_DEBIAN_DOCKER_TO_QEMU_PATH=$_SCRIPTDIR/$CONVERT_DEBIAN_DOCKER_TO_QEMU_NAME
_DOCKER_BUILD_PATH=$_SCRIPTDIR/$DOCKER_BUILD_NAME

[ -f "$_CONVERT_DEBIAN_DOCKER_TO_QEMU_PATH" ] || { echo "Script \`$CONVERT_DEBIAN_DOCKER_TO_QEMU_NAME' not found in $_SCRIPTDIR... Abort."; exit 1; }
[ -f "$_DOCKER_BUILD_PATH"             ] || { echo "Script \`$DOCKER_BUILD_NAME' not found in $_SCRIPTDIR... Abort.";             exit 1; }

_CONVERT_DEBIAN_DOCKER_TO_QEMU_CMD="sh $_CONVERT_DEBIAN_DOCKER_TO_QEMU_PATH"
_DOCKER_BUILD_CMD="sh $_DOCKER_BUILD_PATH"

PROJECT_ARCHIVE_SRC_PATH=source.tar.xz
QEMU_IMAGE_PATH=disk.qcow
OVERWRITE=
QUIET=
NEW_DOCKER_IMAGE_NAME=

_PROJECT_ARCHIVE_SRC_PATH_SPECIFIED=
_QEMU_IMAGE_PATH_SPECIFIED=

while getopts ha:f:oqt: name
do
	case $name in
	h) usage_and_exit_zero;;
	a) _PROJECT_ARCHIVE_SRC_PATH_SPECIFIED=1; PROJECT_ARCHIVE_SRC_PATH=$OPTARG;;
	f) _QEMU_IMAGE_PATH_SPECIFIED=1; QEMU_IMAGE_PATH=$OPTARG;;
	o) OVERWRITE=-o;;
	q) QUIET=-q;;
	t) NEW_DOCKER_IMAGE_NAME="$OPTARG";;
	?) usage_and_exit_nonzero;;
	esac
done
shift $(($OPTIND - 1))

[ $# -ne 2 ] && usage_and_exit_nonzero

AGDA_VERSION=$1
AGDA_STDLIB_VERSION=$2
shift 2

if [ ! -f "$PROJECT_ARCHIVE_SRC_PATH" ]
then
	_DEBUG_MSG="Input file \`$PROJECT_ARCHIVE_SRC_PATH' does not exist... Abort."
	[ -n "$_PROJECT_ARCHIVE_SRC_PATH_SPECIFIED" ] || _DEBUG_MSG="$_DEBUG_MSG (specify with option \`-a ARCHIVE')"
	echo $_DEBUG_MSG
	exit 1
fi

if [ -f "$QEMU_IMAGE_PATH" ] && [ -z "$OVERWRITE" ]
then
	_DEBUG_MSG="Output file \`$QEMU_IMAGE_PATH' exists... Abort. (overwrite with option \`-o'"
	[ -n "$_QEMU_IMAGE_PATH_SPECIFIED" ] || _DEBUG_MSG="$_DEBUG_MSG or specify alternative with option \`-f FILE'"
	_DEBUG_MSG="$_DEBUG_MSG)"
	echo $_DEBUG_MSG
	exit 1
fi

trap '_EXITCODE=$?; trap - INT QUIT TERM EXIT; clean_and_exit' INT QUIT TERM EXIT

if [ -n "$NEW_DOCKER_IMAGE_NAME" ]
then
	_DOCKER_IMAGE_NAME=$NEW_DOCKER_IMAGE_NAME
else
	_DOCKER_IMAGE_NAME=$(random_string [:lower:][:digit:] 16)
fi
_DEBUG_MSG="Building intermediate Docker image $_DOCKER_IMAGE_NAME..."
if [ -n "$QUIET" ]
then
	echo -n "$_DEBUG_MSG "
	_REDIRECT='>/dev/null'
else
	echo $_DEBUG_MSG
	_REDIRECT=
fi
eval $_DOCKER_BUILD_CMD $AGDA_VERSION $AGDA_STDLIB_VERSION $PROJECT_ARCHIVE_SRC_PATH $QUIET -t $_DOCKER_IMAGE_NAME $_REDIRECT
if [ -n "$QUIET" ]
then
	echo Done.
else
	echo Done building Docker image.
fi

eval $_CONVERT_DEBIAN_DOCKER_TO_QEMU_CMD $OVERWRITE -i $_DOCKER_IMAGE_NAME $QEMU_IMAGE_PATH $QEMU_IMAGE_SIZE
