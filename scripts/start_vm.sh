#!/bin/sh

set -e -u

QEMU_ROOT_PASSWORD=root
QEMU_USER_NAME=user
QEMU_USER_PASSWORD=user

#############################################################################
# Start the guest system.
#
#  This will open a graphical console on the host,
#  and attach a virtual network device.
#
#  Start the guest system headless with '-display none'.
#  Use emulation instead of virtualization with '-accel tcg'.
#
# (This is a fork of the ICFP Artifact Evaluation VM Image start script.)
#
#############################################################################

usage () {
	cat <<EOF
Usage: $_SCRIPTNAME [-h] [-f FILE] [-p PORT] [-P] [QEMU_OPTIONS]

Options:
  -h       Show this message
  -f FILE  Use disk image FILE (default: $QEMU_IMAGE_PATH)
  -p PORT  Redirect PORT to SSH port (default: $QEMU_SSH_HOST_PORT)
  -P       Disable redirection to SSH port
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

_SCRIPTNAME=$(basename $0)

QEMU_SSH_GUEST_PORT=22
QEMU_SSH_HOST_PORT=5555
QEMU_IMAGE_PATH=disk.qcow

_QEMU_IMAGE_PATH_SPECIFIED=

# XXX: Carlos might try to run this script with a non-POSIX shell
# whose getopts builtin sets OPTIND to an off-by-one value when an
# option character not contained in the optstring is found
_OPTIND=1
while getopts :hf:p:P name
do
	case $name in
	h) _OPTIND=$(($_OPTIND + 1)); usage_and_exit_zero;;
	f) _OPTIND=$(($_OPTIND + 2)); _QEMU_IMAGE_PATH_SPECIFIED=1; QEMU_IMAGE_PATH=$OPTARG;;
	p) _OPTIND=$(($_OPTIND + 2)); QEMU_SSH_HOST_PORT=$OPTARG;;
	P) _OPTIND=$(($_OPTIND + 1)); QEMU_SSH_HOST_PORT=;;
	?) break;;
	esac
done
shift $(($_OPTIND - 1))

if [ ! -e "$QEMU_IMAGE_PATH" ]
then
	_DEBUG_MSG="Disk image \`$QEMU_IMAGE_PATH' does not exist... Abort."
	[ -n "$_QEMU_IMAGE_PATH_SPECIFIED" ] || _DEBUG_MSG="$_DEBUG_MSG (specify with option \`-f FILE')"
	echo $_DEBUG_MSG
	exit 1
fi

# Expose all features present in the host cpu to the guest.
QEMU_CPU=max

# Give the guest 4GB of RAM.
QEMU_MEM_MB=4096

# Decide what virtualization method to use based on the host system.
case `uname` in
 'Darwin')
        # On Darwin we can use Apple's native
        #  Hardware Virtualization Framework (HVF)
        echo "Darwin host detected."
        QEMU_ACCEL=hvf
        ;;

 'Linux')
        # On Linux use the 'kvm' virtualization method.
        echo "Linux host detected."
        QEMU_ACCEL=kvm
        ;;

  *)    # By default use the Tiny Code Generator that dynamically
        #  converts guest instructions into host instructions.
        #  This is software emulation of the guest processor which
        #  is slow but reliable.
        echo "Unknown host system."
        QEMU_ACCEL=tcg
        ;;
esac

# Try to determine whether video output can be displayed.
if type xset >/dev/null 2>&1 && ! xset -q >/dev/null 2>&1
then
  QEMU_DISPLAY='-display none'
  echo "Command \`xset -q' failed... Will pass \`$QEMU_DISPLAY'."
else
  QEMU_DISPLAY=
fi

echo "Try logging in with the following user information:"
echo ""
echo "  name:      $QEMU_USER_NAME"
echo "  password:  $QEMU_USER_PASSWORD"

if [ -n "$QEMU_SSH_HOST_PORT" ]
then
  echo "Command to log into the guest using SSH:"
  echo ""
  echo "  ssh -p $QEMU_SSH_HOST_PORT -o SendEnv='LANG LC_*' $QEMU_USER_NAME@localhost"
  QEMU_HOSTFWD="hostfwd=tcp::$QEMU_SSH_HOST_PORT-:$QEMU_SSH_GUEST_PORT"
else
  QEMU_HOSTFWD=
fi

# XXX: qemu-system version 7.0.0 fails with `Unknown protocol' if
# filename without leading components contains colons
qemu-system-x86_64 \
        -accel  ${QEMU_ACCEL} \
        -cpu    ${QEMU_CPU} \
        -m      ${QEMU_MEM_MB} \
        -device e1000,netdev=net0 \
        -netdev user,id=net0,${QEMU_HOSTFWD} \
        -hda    $(realpath ${QEMU_IMAGE_PATH}) \
        ${QEMU_DISPLAY} \
        $@
