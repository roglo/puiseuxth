#!/bin/bash
# $Id: show.sh,v 1.2 2013-03-31 05:45:45 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg '$1'"
    ../puiseux$arg --with-sqrt-x "$1" -v -n 1 2>&1
    echo
}

. common.sh
