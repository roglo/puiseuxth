#!/bin/bash
# $Id: show1.sh,v 1.1 2013-03-31 05:58:33 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg '$1'"
    ../puiseux$arg --with-sqrt-x "$1" -v -n 1 2>&1
    echo
}

. common.sh
