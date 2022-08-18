# Debugging Notes

## Running QEMU without a Display

You can start the VM without the console display like so:

```
sh start_vm.sh -display none
```

Then connect to it via SSH.

```
ssh -p 5555 -o SendEnv='LANG LC_*' user@localhost
```


## OSX

- If you are running OSX Catalina and have an old version of QEMU already
  installed then you may see a black screen when the VM starts. One AEC member
  had this problem and resolved it by upgrading to the current version of QEMU.

- There is a known issue with the hypervisor entitlements for QEMU on
  OSX >= 11.0 as described
  [here](https://www.arthurkoziel.com/qemu-on-macos-big-sur/).

  Sandro Stucki has provided the accompanying shell script,
  `fix-qemu-macos.sh`, which can be used to fix the issue.


## Linux

### Problem: KVM Kernel Module Does Not Load

Symptom:

```
$ sh start_vm.sh
[..]
Could not access KVM kernel module: No such file or directory
qemu-system-x86_64: failed to initialize KVM: No such file or directory
```

Check whether the `kvm-intel` or `kvm-amd` module is loading correctly. You
might get:

```
$ sudo modprobe kvm-intel
modprobe: ERROR: could not insert 'kvm_intel': Operation not supported
```

Check the `dmesg` log to see if virtualization has been disabled in the BIOS:

```
$ dmesg | tail
[..]
[  848.697757] kvm: disabled by bios
```

Check your BIOS configuration for a setting like "Intel Virtualization
Technology" and ensure that it is enabled.


### Problem: Virtualization Still Does Not Work

If the KVM virtualization system still doesn't work then you can use plain
emulation via the Tiny Code Generator. This will be slower, but otherwise has
the same functionality.

```
sh start_vm.sh -accel tcg
```
