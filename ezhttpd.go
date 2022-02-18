// Copyright 2019 Seg <seg@haxxed.com>

package main

import "flag"
import "os"
import "path/filepath"
import "fmt"
import "github.com/SegHaxx/ezhttpd/http"

func main(){
	flag.Usage = func() {
		fmt.Println("Usage:",filepath.Base(os.Args[0]),"[options] [path to share]")
		flag.PrintDefaults()
	}
	bind := flag.String("bind",":9000","Bind address")
	flag.Parse()

	webroot := flag.Arg(0)
	if webroot == "" {
		tmp, err := os.Getwd()
		if err != nil {return}
		webroot = tmp
	}
	webroot = filepath.Clean(webroot)

	hostname := ""
	if (*bind)[0] == ':' {
		tmp, err := os.Hostname()
		if err == nil {
			hostname = tmp
	}}

	fmt.Print("Sharing ",webroot," on http://",hostname,*bind,"/\n")

	http.Handle("/", http.FileServer(http.Dir(webroot)))
	fmt.Println(http.ListenAndServe((*bind),
		http.HandlerFunc(func(w http.ResponseWriter,r *http.Request){
			http.DefaultServeMux.ServeHTTP(w,r)
			fmt.Println(r.RemoteAddr,r.Method,r.URL.Path)
	})))
}
