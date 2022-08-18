# syntax=docker/dockerfile:1
FROM debian:bullseye AS build

SHELL ["/bin/sh", "-e", "-c"]

ARG ROOT_HOME=/root

RUN <<EOF
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y unp wget
apt-get install -y cabal-install
apt-get install -y alex happy zlib1g-dev
EOF

RUN <<EOF
cat >>/etc/skel/.profile <<"_EOF"

# set PATH so it includes user's cabal bin if it exists
if [ -d "$HOME/.cabal/bin" ] ; then
    PATH="$HOME/.cabal/bin:$PATH"
fi
_EOF
cp /etc/skel/.profile $HOME/
EOF

ARG SOURCES_PATH=$ROOT_HOME/sources
ARG BUILDS_PATH=$ROOT_HOME/builds
ARG PACKAGES_PATH=$ROOT_HOME/packages

ENV SOURCES_PATH=$SOURCES_PATH
ENV BUILDS_PATH=$BUILDS_PATH
ENV PACKAGES_PATH=$PACKAGES_PATH

RUN mkdir -p $SOURCES_PATH $BUILDS_PATH $PACKAGES_PATH

ARG AGDA_VERSION=

ARG AGDA_PACKAGE_NAME=agda-$AGDA_VERSION.tar.gz

ARG AGDA_SOURCE_ARCHIVE_URL=https://github.com/agda/agda/archive/v${AGDA_VERSION}.tar.gz
ARG AGDA_SOURCE_ARCHIVE_EXT=tar.gz
ARG AGDA_SOURCE_ARCHIVE_ROOT_NAME=agda-$AGDA_VERSION

ARG AGDA_SOURCE_ARCHIVE_PATH=$SOURCES_PATH/agda-$AGDA_VERSION.$AGDA_SOURCE_ARCHIVE_EXT
ARG AGDA_BUILD_PATH=$BUILDS_PATH/agda-$AGDA_VERSION
ARG AGDA_PACKAGE_PATH=$PACKAGES_PATH/$AGDA_PACKAGE_NAME

ENV AGDA_VERSION=$AGDA_VERSION

ENV AGDA_SOURCE_ARCHIVE_URL=$AGDA_SOURCE_ARCHIVE_URL

ENV AGDA_SOURCE_ARCHIVE_PATH=$AGDA_SOURCE_ARCHIVE_PATH
ENV AGDA_BUILD_PATH=$AGDA_BUILD_PATH
ENV AGDA_PACKAGE_PATH=$AGDA_PACKAGE_PATH

RUN <<EOF
CABAL_DIR_PATH=$HOME/.cabal

_CABAL_PACKAGE_DB_PATH=$CABAL_DIR_PATH/store/ghc-$(ghc --numeric-version)/package.db

_AGDA_BUILD_ROOT_PATH=$AGDA_BUILD_PATH/$AGDA_SOURCE_ARCHIVE_ROOT_NAME
_AGDA_PACKAGE_FILES_PATH=$(mktemp -d --tmpdir agda-$AGDA_VERSION.XXXXXXX)
_AGDA_PACKAGE_FILES_LIST=$(mktemp --tmpdir agda-$AGDA_VERSION-files.XXXXXXX)

mkdir -p $AGDA_BUILD_PATH/

# download
wget -O $AGDA_SOURCE_ARCHIVE_PATH $AGDA_SOURCE_ARCHIVE_URL

# unpack
cd $AGDA_BUILD_PATH/
unp $AGDA_SOURCE_ARCHIVE_PATH

# install dependencies
cd $_AGDA_BUILD_ROOT_PATH/
cabal update
cabal build --only-dependencies

# build
cd $_AGDA_BUILD_ROOT_PATH/
runhaskell Setup.hs configure --package-db=$_CABAL_PACKAGE_DB_PATH --enable-relocatable --prefix=$CABAL_DIR_PATH
runhaskell Setup.hs build

# package
cd $_AGDA_BUILD_ROOT_PATH/
runhaskell Setup.hs copy --destdir=$_AGDA_PACKAGE_FILES_PATH/
find $_AGDA_PACKAGE_FILES_PATH/ -mindepth 1 -printf '%P\0' >$_AGDA_PACKAGE_FILES_LIST
tar -C $_AGDA_PACKAGE_FILES_PATH/ -c -a -f $AGDA_PACKAGE_PATH --transform "s|^$(realpath --relative-to=/ $CABAL_DIR_PATH)/||" --no-recursion --null -T $_AGDA_PACKAGE_FILES_LIST
rm -r $_AGDA_PACKAGE_FILES_PATH/ $_AGDA_PACKAGE_FILES_LIST
EOF

ARG AGDA_INSTALL_PREFIX=/usr
ARG AGDA_DIR_PATH=$ROOT_HOME/.agda
ARG AGDA_DATA_PATH=$ROOT_HOME/.local/share/agda
ARG AGDA_LIB_PATH=$AGDA_DATA_PATH/lib

ENV AGDA_DIR_PATH=$AGDA_DIR_PATH
ENV AGDA_DATA_PATH=$AGDA_DATA_PATH
ENV AGDA_LIB_PATH=$AGDA_LIB_PATH

RUN <<EOF
tar -C $AGDA_INSTALL_PREFIX/ -x -f $AGDA_PACKAGE_PATH
mkdir -p $AGDA_DIR_PATH/ $AGDA_DATA_PATH/ $AGDA_LIB_PATH/
EOF

ARG AGDA_STDLIB_VERSION=

ARG AGDA_STDLIB_PACKAGE_NAME=agda-stdlib-$AGDA_STDLIB_VERSION.tar.gz
ARG AGDA_STDLIB_PACKAGE_ROOT_NAME=agda-stdlib-$AGDA_STDLIB_VERSION
ARG AGDA_STDLIB_PACKAGE_AGDA_LIB_NAME=standard-library.agda-lib

ARG AGDA_STDLIB_SOURCE_ARCHIVE_URL=https://github.com/agda/agda-stdlib/archive/v${AGDA_STDLIB_VERSION}.tar.gz
ARG AGDA_STDLIB_SOURCE_ARCHIVE_EXT=tar.gz
ARG AGDA_STDLIB_SOURCE_ARCHIVE_ROOT_NAME=agda-stdlib-$AGDA_STDLIB_VERSION
ARG AGDA_STDLIB_SOURCE_ARCHIVE_AGDA_LIB_NAME=standard-library.agda-lib

ARG AGDA_STDLIB_SOURCE_ARCHIVE_PATH=$SOURCES_PATH/agda-stdlib-$AGDA_STDLIB_VERSION.$AGDA_STDLIB_SOURCE_ARCHIVE_EXT
ARG AGDA_STDLIB_BUILD_PATH=$BUILDS_PATH/agda-stdlib-$AGDA_STDLIB_VERSION
ARG AGDA_STDLIB_PACKAGE_PATH=$PACKAGES_PATH/$AGDA_STDLIB_PACKAGE_NAME

ENV AGDA_STDLIB_VERSION=$AGDA_STDLIB_VERSION

ENV AGDA_STDLIB_SOURCE_ARCHIVE_URL=$AGDA_STDLIB_SOURCE_ARCHIVE_URL

ENV AGDA_STDLIB_SOURCE_ARCHIVE_PATH=$AGDA_STDLIB_SOURCE_ARCHIVE_PATH
ENV AGDA_STDLIB_BUILD_PATH=$AGDA_STDLIB_BUILD_PATH
ENV AGDA_STDLIB_PACKAGE_PATH=$AGDA_STDLIB_PACKAGE_PATH

RUN <<EOF
_AGDA_STDLIB_BUILD_ROOT_PATH=$AGDA_STDLIB_BUILD_PATH/$AGDA_STDLIB_SOURCE_ARCHIVE_ROOT_NAME
_AGDA_STDLIB_PACKAGE_FILES_PATH=$(mktemp -d --tmpdir agda-stdlib-$AGDA_STDLIB_VERSION.XXXXXXX)
_AGDA_STDLIB_PACKAGE_FILES_LIST=$(mktemp --tmpdir agda-stdlib-$AGDA_STDLIB_VERSION-files.XXXXXXX)

mkdir -p $AGDA_STDLIB_BUILD_PATH/

# download
wget -O $AGDA_STDLIB_SOURCE_ARCHIVE_PATH $AGDA_STDLIB_SOURCE_ARCHIVE_URL

# unpack
cd $AGDA_STDLIB_BUILD_PATH/
unp $AGDA_STDLIB_SOURCE_ARCHIVE_PATH

# build
cd $_AGDA_STDLIB_BUILD_ROOT_PATH/
cabal run GenerateEverything
agda -i. -isrc Everything.agda

# package
cd $_AGDA_STDLIB_BUILD_ROOT_PATH/
mkdir -p $_AGDA_STDLIB_PACKAGE_FILES_PATH/
mkdir -p $_AGDA_STDLIB_PACKAGE_FILES_PATH/$AGDA_STDLIB_PACKAGE_ROOT_NAME/
cp $AGDA_STDLIB_SOURCE_ARCHIVE_AGDA_LIB_NAME $_AGDA_STDLIB_PACKAGE_FILES_PATH/$AGDA_STDLIB_PACKAGE_ROOT_NAME/$AGDA_STDLIB_PACKAGE_AGDA_LIB_NAME
cp -r src/ $_AGDA_STDLIB_PACKAGE_FILES_PATH/$AGDA_STDLIB_PACKAGE_ROOT_NAME/
cp -r _build/ $_AGDA_STDLIB_PACKAGE_FILES_PATH/$AGDA_STDLIB_PACKAGE_ROOT_NAME/
find $_AGDA_STDLIB_PACKAGE_FILES_PATH/ -mindepth 1 -printf '%P\0' >$_AGDA_STDLIB_PACKAGE_FILES_LIST
tar -C $_AGDA_STDLIB_PACKAGE_FILES_PATH/ -c -a -f $AGDA_STDLIB_PACKAGE_PATH --no-recursion --null -T $_AGDA_STDLIB_PACKAGE_FILES_LIST
rm -r $_AGDA_STDLIB_PACKAGE_FILES_PATH/ $_AGDA_STDLIB_PACKAGE_FILES_LIST
EOF

RUN <<EOF
tar -C $AGDA_LIB_PATH/ -x -f $AGDA_STDLIB_PACKAGE_PATH
echo $AGDA_LIB_PATH/$AGDA_STDLIB_PACKAGE_ROOT_NAME/$AGDA_STDLIB_PACKAGE_AGDA_LIB_NAME >>$AGDA_DIR_PATH/libraries
EOF

USER $USER_NAME
WORKDIR $USER_HOME
CMD bash -l

ENV DOCKER_REPOSITORY=fitch-style
ENV DOCKER_BASE_IMAGE=debian:bullseye
ENV DOCKER_STAGE=build


FROM debian:bullseye AS base

SHELL ["/bin/sh", "-e", "-c"]

RUN <<EOF
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y locales
apt-get install -y sudo
#apt-get install -y less man
apt-get install -y bash-completion vim-nox
EOF

ARG TIMEZONE=Europe/Berlin
ARG LOCALE=en_US
ARG ROOT_HOME=/root
ARG ROOT_PASSWORD=root
ARG USER_NAME=user
ARG USER_HOME=/home/$USER_NAME
ARG USER_GROUP=$USER_NAME
ARG USER_PASSWORD=$USER_NAME

RUN ln -sf /usr/share/zoneinfo/$TIMEZONE /etc/localtime

RUN <<EOF
sed -i -e "/^# $LOCALE.UTF-8 UTF-8$/ s/^# //" /etc/locale.gen
locale-gen
echo LANG=$LOCALE.UTF-8 >/etc/locale.conf
EOF

RUN <<EOF
sed -i -e 's/^%sudo	ALL=(ALL:ALL) ALL$/%sudo ALL=(ALL:ALL) NOPASSWD: ALL/' /etc/sudoers
EOF

RUN apt-get install -y gawk

RUN <<EOF
awk -i inplace -f - /etc/bash.bashrc <<_EOF
u && /^$/                                          { u=0              }
u                                                  { sub(/^#/,"",\$0) }
/^# enable bash completion in interactive shells$/ { u=1              }
                                                   { print            }
_EOF
cat >>/etc/skel/.bashrc <<_EOF

set -o noclobber
set -o vi

alias ll='ls -l -h -F'
alias cp='cp -i'
alias mv='mv -i'
alias rm='rm -i'
_EOF
cat >>/etc/skel/.profile <<"_EOF"

# set PATH so it includes user's cabal bin if it exists
if [ -d "$HOME/.cabal/bin" ] ; then
    PATH="$HOME/.cabal/bin:$PATH"
fi
_EOF
cp /etc/skel/.bashrc /etc/skel/.profile $HOME/
EOF

RUN apt-get purge -y gawk

RUN <<EOF
groupadd $USER_GROUP
useradd -m -d $USER_HOME -g $USER_GROUP -G sudo -s /bin/bash $USER_NAME
chpasswd <<_EOF
root:$ROOT_PASSWORD
$USER_NAME:$USER_PASSWORD
_EOF
EOF

USER root
ENV LANG=en_US.UTF-8
WORKDIR $ROOT_HOME
CMD bash -l

ENV DOCKER_REPOSITORY=fitch-style
ENV DOCKER_BASE_IMAGE=debian:bullseye
ENV DOCKER_STAGE=base


FROM base AS project

SHELL ["/bin/sh", "-e", "-c"]

RUN <<EOF
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y emacs-nox
EOF

ARG PACKAGES_PATH=$ROOT_HOME/packages
ARG MNT_PATH=/mnt

ARG AGDA_VERSION=

ARG AGDA_PACKAGE_NAME=agda-$AGDA_VERSION.tar.gz

ENV AGDA_VERSION=$AGDA_VERSION

ARG AGDA_INSTALL_PREFIX=/usr
ARG AGDA_DIR_PATH=$USER_HOME/.agda
ARG AGDA_DATA_PATH=$USER_HOME/.local/share/agda
ARG AGDA_LIB_PATH=$AGDA_DATA_PATH/lib

ENV AGDA_DIR_PATH=$AGDA_DIR_PATH
ENV AGDA_DATA_PATH=$AGDA_DATA_PATH
ENV AGDA_LIB_PATH=$AGDA_LIB_PATH

RUN --mount=type=bind,from=build,source=$PACKAGES_PATH,target=$MNT_PATH <<EOF
cd $MNT_PATH/
tar -C $AGDA_INSTALL_PREFIX/ -x -f $AGDA_PACKAGE_NAME
EOF

USER $USER_NAME

RUN mkdir -p $AGDA_DIR_PATH/ $AGDA_DATA_PATH/ $AGDA_LIB_PATH/

RUN <<EOF
cat <<_EOF >>$HOME/.emacs
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))

;; - "when you press the \`Ctrl\` and \`,\` keys, the terminal treats it
;;   the same as if you only pressed \`,\`"
;;   (https://lists.chalmers.se/pipermail/agda/2018/010543.html)
;;
;; - wrap in with-eval-after-load "agda2-mode" because
;;   agda2-set-program-version (switching Agda version) runs
;;   unload-feature 'agda2-mode, which in turn runs remove-hook
;;   'agda2-mode-hook
;;
(with-eval-after-load "agda2-mode"
 (add-hook 'agda2-mode-hook
  (lambda ()
   (define-key agda2-mode-map (kbd "C-c SPC") 'agda2-give)
   (define-key agda2-mode-map (kbd "C-c m")   'agda2-elaborate-give)
   (define-key agda2-mode-map (kbd "C-c ,")   'agda2-goal-and-context)
   (define-key agda2-mode-map (kbd "C-c ;")   'agda2-goal-and-context-and-checked)
   (define-key agda2-mode-map (kbd "C-c .")   'agda2-goal-and-context-and-inferred)
   (define-key agda2-mode-map (kbd "C-c =")   'agda2-show-constraints)
   (define-key agda2-mode-map (kbd "C-c ?")   'agda2-show-goals)
   (define-key agda2-mode-map (kbd "C-c o")   'agda2-module-contents-maybe-toplevel)
   (define-key agda2-mode-map (kbd "C-c z")   'agda2-search-about-toplevel)
   (define-key agda2-mode-map (kbd "C-c s")   'agda2-solve-maybe-all))))
_EOF
EOF

ARG AGDA_STDLIB_VERSION=

ARG AGDA_STDLIB_PACKAGE_NAME=agda-stdlib-$AGDA_STDLIB_VERSION.tar.gz
ARG AGDA_STDLIB_PACKAGE_ROOT_NAME=agda-stdlib-$AGDA_STDLIB_VERSION
ARG AGDA_STDLIB_PACKAGE_AGDA_LIB_NAME=standard-library.agda-lib

USER $USER_NAME

ENV AGDA_STDLIB_VERSION=$AGDA_STDLIB_VERSION

RUN --mount=type=bind,from=build,source=$PACKAGES_PATH,target=$MNT_PATH <<EOF
cd $MNT_PATH/
tar -C $AGDA_LIB_PATH/ -x -f $AGDA_STDLIB_PACKAGE_NAME
echo $AGDA_LIB_PATH/$AGDA_STDLIB_PACKAGE_ROOT_NAME/$AGDA_STDLIB_PACKAGE_AGDA_LIB_NAME >>$AGDA_DIR_PATH/libraries
EOF

USER root

RUN apt-get install -y unp unzip xz-utils

ARG PROJECT_ARCHIVE_SRC_RELPATH

USER $USER_NAME

RUN --mount=target=$MNT_PATH <<EOF
cd $HOME/
unp $MNT_PATH/$PROJECT_ARCHIVE_SRC_RELPATH
EOF

USER root

RUN apt-get purge -y unp unzip xz-utils

USER root

# install kernel and initrd for booting the image, install sshd for
# another way to interact with the booted image
RUN <<EOF
export DEBIAN_FRONTEND=noninteractive
apt-get install -y console-setup ifupdown linux-image-amd64 systemd-sysv
apt-get install -y openssh-server
EOF

USER root

RUN apt-get purge --auto-remove -y && apt-get clean

USER $USER_NAME
ENV LANG=en_US.UTF-8
WORKDIR $USER_HOME
CMD bash -l

ENV DOCKER_REPOSITORY=fitch-style
ENV DOCKER_BASE_IMAGE=base
ENV DOCKER_STAGE=project
