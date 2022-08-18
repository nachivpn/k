#!/bin/sh

set -e -u

HOSTNAME=vm
IFACE=eth

usage () {
	cat <<EOF
Usage: $_SCRIPTNAME -d DOCKERFILE  [OPTIONS] FILE SIZE
       $_SCRIPTNAME -i DOCKERIMAGE [OPTIONS] FILE SIZE

Options:
  -h              Show this message
  -d DOCKERFILE   Create QEMU image FILE of SIZE from DOCKERFILE
  -i DOCKERIMAGE  Create QEMU image FILE of SIZE from DOCKERIMAGE
  -f FMT          Use QEMU image format FMT (default: $QEMU_IMAGE_FORMAT)
  -m MBRBIN       Install MBRBIN into master boot record
                  (default: $MBR_BIN_PATH)
  -o              Overwrite FILE if it exists
  -q              Suppress Docker build output
  -t NAME         Keep the intermediate Docker image built from
                  DOCKERFILE as NAME
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
	[ -z "${_DOCKER_ID:+x}"          ] || [ -z "$(docker container ls -a -q -f id=$_DOCKER_ID)" ] || docker container rm $_DOCKER_ID >/dev/null
	[ -z "${_DOCKER_IMAGE_NAME:+x}"  ] || [ -z "$DOCKERFILE_PATH" ] || [ -n "$NEW_DOCKER_IMAGE_NAME" ] || ! docker inspect $_DOCKER_IMAGE_NAME >/dev/null 2>&1 || docker image rm $_DOCKER_IMAGE_NAME >/dev/null
	[ -z "${_BUILD_CONTEXT_PATH:+x}" ] || [ ! -e "$_BUILD_CONTEXT_PATH" ] || rm -r $_BUILD_CONTEXT_PATH
	[ -z "${_WORKDIR:+x}"            ] || [ ! -e "$_WORKDIR" ]            || rm -r $_WORKDIR
	exit $_EXITCODE
}

random_string () {
	ARRAY=$1
	CHARS=$2
	tr -dc $ARRAY </dev/urandom | head -c $CHARS
}

tar_replace () {
	ARCHIVE=$1
	FILE=$2
	shift 2

	tar -t -f $ARCHIVE $FILE >/dev/null 2>&1 && tar --delete -f $ARCHIVE $FILE
	tar -r -f $ARCHIVE $@ $FILE
}

assert_command_found () {
	type $1 >/dev/null 2>&1 || { echo "Command \`$1' not found... Abort."; exit 1; }
}

assert_command_found qemu-img
assert_command_found guestfish
assert_command_found sqfstar
assert_command_found bsdtar

_SCRIPTNAME=$(basename $0)

DOCKERFILE_PATH=
DOCKER_IMAGE_NAME=
QEMU_IMAGE_FORMAT=qcow2
MBR_BIN_PATH=$(find /usr/lib/syslinux -name mbr.bin -print -quit 2>/dev/null) && test -n "$MBR_BIN_PATH" || MBR_BIN_PATH=mbr.bin
OVERWRITE=
QUIET=
NEW_DOCKER_IMAGE_NAME=

_MBR_BIN_PATH_SPECIFIED=

while getopts hd:i:f:m:oqt name
do
	case $name in
	h) usage_and_exit_zero;;
	d) DOCKERFILE_PATH=$OPTARG;;
	i) DOCKER_IMAGE_NAME=$OPTARG;;
	f) QEMU_IMAGE_FORMAT=$OPTARG;;
	m) _MBR_BIN_PATH_SPECIFIED=1; MBR_BIN_PATH=$OPTARG;;
	o) OVERWRITE=1;;
	q) QUIET=-q;;
	t) NEW_DOCKER_IMAGE_NAME=$OPTARG;;
	?) usage_and_exit_nonzero;;
	esac
done
shift $(($OPTIND - 1))

[ $# -ne 2 ] && usage_and_exit_nonzero

QEMU_IMAGE_PATH=$1
QEMU_IMAGE_SIZE=$2
shift 2

if ([ -z "$DOCKERFILE_PATH" ] && [ -z "$DOCKER_IMAGE_NAME" ]) || ([ -n "$DOCKERFILE_PATH" ] && [ -n "$DOCKER_IMAGE_NAME" ])
then
	echo "Specify either option \`-d DOCKERFILE' or \`-i DOCKERIMAGE'... Abort."
	exit 1
fi

if [ -n "$NEW_DOCKER_IMAGE_NAME" ] && [ -z "$DOCKERFILE_PATH" ]
then
	echo "Option \`-t NAME' but not \`-d DOCKERFILE' specified... Abort."
	exit 1
fi

if [ -n "$DOCKERFILE_PATH" ] && [ ! -f "$DOCKERFILE_PATH" ]
then
	echo "Input file \`$DOCKERFILE_PATH' does not exist... Abort."
	exit 1
fi

if [ -n "$DOCKER_IMAGE_NAME" ] && [ ! docker image inspect $DOCKER_IMAGE_NAME >/dev/null 2>&1 ]
then
	echo "Input image \`$DOCKER_IMAGE_NAME' does not exist... Abort."
	exit 1
fi

if [ ! -f "$MBR_BIN_PATH" ]
then
	_DEBUG_MSG="Input file \`$MBR_BIN_PATH' does not exist... Abort."
	[ -n "$_MBR_BIN_PATH_SPECIFIED" ] || _DEBUG_MSG="$_DEBUG_MSG (specify with option \`-m MBRBIN')"
	echo $_DEBUG_MSG
	exit 1
fi

if [ -f "$QEMU_IMAGE_PATH" ] && [ -z "$OVERWRITE" ]
then
	echo "Output file \`$QEMU_IMAGE_PATH' exists... Abort. (overwrite with option \`-o')"
	exit 1
fi

trap '_EXITCODE=$?; trap - INT QUIT TERM EXIT; clean_and_exit' INT QUIT TERM EXIT

_WORKDIR=$(mktemp -d --tmpdir $_SCRIPTNAME.XXXXXXXXXX)

if [ -n "$DOCKERFILE_PATH" ]
then
	_DEBUG_MSG="Building intermediate Docker image"
	if [ -n "$NEW_DOCKER_IMAGE_NAME" ]
	then
		_DEBUG_MSG="$_DEBUG_MSG $NEW_DOCKER_IMAGE_NAME"
		_DOCKER_IMAGE_NAME=$NEW_DOCKER_IMAGE_NAME
	else
		_DOCKER_IMAGE_NAME=$(random_string [:lower:][:digit:] 16)
	fi
	_DEBUG_MSG="$_DEBUG_MSG from $DOCKERFILE_PATH..."
	if [ -n "$QUIET" ]
	then
		echo -n "$_DEBUG_MSG "
		_REDIRECT='>/dev/null'
	else
		echo $_DEBUG_MSG
		_REDIRECT=
	fi
	_BUILD_CONTEXT_PATH=$(mktemp -d --tmpdir ${_SCRIPTNAME}_build_context.XXXXXXXXXX)
	cp $DOCKERFILE_PATH $_BUILD_CONTEXT_PATH/
	eval DOCKER_BUILDKIT=1 docker build $QUIET -f $_BUILD_CONTEXT_PATH/$(basename $DOCKERFILE_PATH) -t $_DOCKER_IMAGE_NAME $_BUILD_CONTEXT_PATH $_REDIRECT
	if [ -n "$QUIET" ]
	then
		echo Done.
	else
		echo Done building Docker image.
	fi
else
	_DOCKER_IMAGE_NAME=$DOCKER_IMAGE_NAME
fi

echo -n "Exporting filesystem from Docker image $_DOCKER_IMAGE_NAME... "

DISTFS_NOCOMPRESS='-noD -noF'

_DOCKER_ID=$(docker create $_DOCKER_IMAGE_NAME)
_DISTTAR=$_WORKDIR/docker-export
_DISTDIR=$_WORKDIR/root
_DISTFS=$_WORKDIR/mksquashfs

mkdir -p $_DISTDIR

_EXTLINUX_CONF_PATH=$_DISTDIR/extlinux.conf
_FSTAB_PATH=$_DISTDIR/etc/fstab
_HOSTNAME_PATH=$_DISTDIR/etc/hostname
_HOSTS_PATH=$_DISTDIR/etc/hosts
_INTERFACE_PATH=$_DISTDIR/etc/network/interfaces.d/$IFACE
_CONSOLE_SETUP_PATH=$_DISTDIR/etc/default/console-setup
_KEYBOARD_PATH=$_DISTDIR/etc/default/keyboard

mkdir -p $(dirname $_EXTLINUX_CONF_PATH)
cat >$_EXTLINUX_CONF_PATH <<EOF
default linux

label linux
  say    Booting linux
  kernel /vmlinuz
  initrd /initrd.img
  append root=/dev/sda1 ro noresume console=tty0 console=ttyS0
EOF
chmod 644 $_EXTLINUX_CONF_PATH

mkdir -p $(dirname $_FSTAB_PATH)
cat >$_FSTAB_PATH <<EOF
/dev/sda1 / ext4 rw,relatime 0 1
EOF
chmod 644 $_FSTAB_PATH

mkdir -p $(dirname $_HOSTNAME_PATH)
cat >$_HOSTNAME_PATH <<EOF
$HOSTNAME
EOF
chmod 644 $_HOSTNAME_PATH

mkdir -p $(dirname $_HOSTS_PATH)
cat >$_HOSTS_PATH <<EOF
127.0.0.1 localhost
::1       localhost
127.0.0.1 $HOSTNAME
EOF
chmod 644 $_HOSTS_PATH

mkdir -p $(dirname $_INTERFACE_PATH)
cat >$_INTERFACE_PATH <<EOF
rename /en*=$IFACE
allow-hotplug $IFACE
iface $IFACE inet dhcp
EOF
chmod 644 $_INTERFACE_PATH

mkdir -p $(dirname $_CONSOLE_SETUP_PATH)
cat >$_CONSOLE_SETUP_PATH <<EOF
# CONFIGURATION FILE FOR SETUPCON

# Consult the console-setup(5) manual page.

ACTIVE_CONSOLES="/dev/tty[1-6]"

CHARMAP="UTF-8"

CODESET="guess"
FONTFACE="Terminus"
FONTSIZE="10x18"

VIDEOMODE=

# The following is an example how to use a braille font
# FONT='lat9w-08.psf.gz brl-8x8.psf'
EOF
chmod 644 $_CONSOLE_SETUP_PATH

mkdir -p $(dirname $_KEYBOARD_PATH)
cat >$_KEYBOARD_PATH <<EOF
# KEYBOARD CONFIGURATION FILE

# Consult the keyboard(5) manual page.

XKBMODEL="pc105"
XKBLAYOUT="se"
XKBVARIANT="nodeadkeys"
XKBOPTIONS="compose:prsc,caps:escape_shifted_capslock"

BACKSPACE="guess"
EOF
chmod 644 $_KEYBOARD_PATH

# XXX: - guestfish version 1.48.4 tar-in fails with `Cannot allocate
#        memory'
#      - Docker version 20.10.17 seems to export POSIX tar archives,
#        which sqfstar version 4.5.1 and GNU tar --delete version
#        1.34 do not seem to handle correctly (symbolic link targets
#        seem to get stripped, or symbolic links seem to get lost
#        entirely)
docker export $_DOCKER_ID | bsdtar -c -f $_DISTTAR --format=ustar @-
find $_DISTDIR -type f,l -printf '%P\n' | while read _FILE ; do tar_replace $_DISTTAR $_FILE -C $_DISTDIR --owner=0:0 --group=0:0 ; done
sqfstar -quiet -no-progress $DISTFS_NOCOMPRESS $_DISTFS <$_DISTTAR
rm $_DISTTAR

echo Done.

echo -n "Creating QEMU image $QEMU_IMAGE_PATH... "
_QEMU_IMAGE_RAW=$_WORKDIR/disk-image
qemu-img create -q $_QEMU_IMAGE_RAW $QEMU_IMAGE_SIZE
guestfish <<EOF >/dev/null
add-drive $_QEMU_IMAGE_RAW
add-drive-ro $_DISTFS
launch
part-disk /dev/sda mbr
mkfs ext4 /dev/sda1
mount /dev/sda1 /
mkdir /squashfs/
mount /dev/sdb /squashfs/
glob cp-a /squashfs/* /
umount /squashfs/
rmdir /squashfs/
extlinux /
upload $MBR_BIN_PATH /mbr.bin
copy-file-to-device /mbr.bin /dev/sda
part-set-bootable /dev/sda 1 true
EOF
# XXX: qemu-img version 7.0.0 fails with `Unknown protocol' if
# filename without leading components contains colons
qemu-img convert -q -O $QEMU_IMAGE_FORMAT $_QEMU_IMAGE_RAW $(realpath $QEMU_IMAGE_PATH)
echo Done.
