# ezhttpd

A minimal, lightweight, self-contained and easy to use httpd for sharing an entire directory tree.

ezhttpd is great for streaming media to Kodi media players, and is also handy for sharing files with internet connected retro computers.

A pre-built Windows binary is provided, ezhttpd can be easily built for use on Linux, macOS and anywhere else [golang](https://go.dev/) is found.

![image](https://user-images.githubusercontent.com/8746882/69205823-e8639500-0aff-11ea-86ac-d224a69c9cec.png)

# Windows Usage Examples

Throw ezhttpd.exe in your Videos directory, and run it. Add the URL `http://[hostname or ip]:9000/` as a source in Kodi. Easy.

Drag-and-drop a directory on to ezhttpd.exe and it will be shared.

Use a shortcut, batch file or script to start ezhttpd.exe with custom options. `-bind` can be used to use a different port or bind to a specific IP.

**Beware:** If you change the port number, Windows Firewall will not notice and quietly block connections. If you mysteriously can't connect, clear all ezhttpd.exe entries out of Windows Firewall and restart ezhttpd.

```
Usage: ezhttpd.exe [options] [path to share]
  -bind string
        Bind address (default ":9000")
```

# How to Build ezhttpd

To use ezhttpd on Linux, macOS or most other operating systems, [install Go](https://go.dev/doc/install) and run `go install github.com/SegHaxx/ezhttpd@latest`

The ezhttpd binary will now be available in the Go binary directory, which can be found with `echo $(go env GOPATH)/bin`

## Why ezhttpd?

I have a bunch of media files on a Windows 10 PC that I wish to stream to a Kodi media player. This shouldn't be hard, right? Wrong. Getting Kodi to connect to Windows 10 filesharing is hopeless; and DLNA is buggy, bloaty and crashes my raspi.

How about a plain old HTTP server? lighthttpd works, but how about something lighter? I tried a variety of tiny httpd servers, but they all either do not serve directory listings, or do not support range requests, allowing seeking in Kodi. The only thing even close to working was golang's built in httpd library. However it's directory listings are... minimal, so you do not see file sizes in Kodi.

How about something that comes in a single exe and requires no configuration?

Thus, ezhttpd: I forked the entire httpd package, and patched it to supply full directory listings using a template shamelessly stolen from lighthttpd. And to keep the binary size down I stripped out things not needed like CGI, cookies, crypto and HTTP/2. As such, ezhttpd is intended for sharing on a local LAN with no expectation of strong security.

## TODO
* support sharing multiple directory trees. (~/Videos/ *and* ~/Music/)
* a GUI with a tray icon
