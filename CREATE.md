# Normalization for Fitch-Style Modal Calculi (Scripts)

The directory `scripts` contains scripts to help build the artifact
accompanying the paper *Normalization for Fitch-Style Modal Calculi*.

## Dependencies

To create a QEMU image:

- bsdtar
- docker
- libguestfs
- qemu-img
- squashfs
- syslinux

To run the QEMU image:

- qemu-system

## Create

To create a QEMU image `disk.qcow` with Agda 2.6.2.2 and Agda
standard library 1.7.1 installed, and the Agda code from the branch
`icfp22-artifact` extracted to a folder `source` in the user home
directory in the image use:

```shell
PROJECT_ARCHIVE_ROOT_NAME=source
git archive --format=tar --prefix=$PROJECT_ARCHIVE_ROOT_NAME/ icfp22-artifact | xz >source.tar.xz
sh scripts/create_image.sh -q 2.6.2.2 1.7.1
```

To create an archive `vm.tar.xz` containing the QEMU image
`disk.qcow`, `README.md`, `Debugging.md`, the start script
`start_vm.sh`, and `fix-qemu-macos.sh` use:

```shell
sed -e "s/PROJECT_ARCHIVE_ROOT_NAME/$PROJECT_ARCHIVE_ROOT_NAME/" data/README.md.template >data/README.md && \
tar -c -f vm.tar --transform 's|^.*/||;s|^|vm/|' data/{README.md,Debugging.md} scripts/{start_vm.sh,fix-qemu-macos.sh} disk.qcow && \
rm data/README.md
xz -v vm.tar
```

## Run

To run the QEMU image `disk.qcow` use:

```shell
sh scripts/start_vm.sh
```

See the command output for the login information.
