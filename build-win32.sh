#!/bin/sh
STRIP=i686-w64-mingw32-strip
command -v $STRIP >/dev/null 2>&1 || STRIP=strip
GOOS=windows GOARCH=386 go build -gcflags "-m" -ldflags="-s -w"
$STRIP -s --strip-unneeded -R .comment -R .note -R .note.ABI-tag ezhttpd.exe
