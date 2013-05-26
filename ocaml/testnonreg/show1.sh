#!/bin/bash
# $Id: show1.sh,v 1.3 2013-05-26 20:00:19 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg --with-sqrt-x \"$1\" -v -n 1 -d"
    ../puiseux$arg --with-sqrt-x "$1" -v -n 1 -d 2>&1
    echo
}

. common.sh
