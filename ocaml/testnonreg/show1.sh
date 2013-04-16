#!/bin/bash
# $Id: show1.sh,v 1.2 2013-04-16 14:06:38 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg '$1'"
    ../puiseux$arg --with-sqrt-x "$1" -v -n 1 -d 2>&1
    echo
}

. common.sh
