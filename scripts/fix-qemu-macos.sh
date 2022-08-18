#!/bin/sh

# Script to fix hypervisor entitlements for QEmu on macOS 11.0 Big Sur
# or later.
#
# Based on the instructions given at
#
#   https://www.arthurkoziel.com/qemu-on-macos-big-sur/
#
# If you get a QEmu error of the form
#
#   qemu-system-x86_64: -accel hvf: Error: HV_ERROR
#   ...
#
# try running this script.
#
# Requirements: You must have the XCode command line tools installed.
# You can get them using
#
#   sudo xcode-select --install

cat > entitlements.xml <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>com.apple.security.hypervisor</key>
    <true/>
</dict>
</plist>
EOF

codesign -s - --entitlements entitlements.xml --force /usr/local/bin/qemu-system-x86_64
