#!/bin/bash
go build -gcflags "-m" -ldflags="-s -w"
strip -s --strip-unneeded -R .comment -R .note -R .note.ABI-tag ezhttpd.exe
