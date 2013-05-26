#!/bin/bash
# $Id: show4.sh,v 1.3 2013-05-26 20:00:19 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg -e 3 \"$1\" -d"
    ../puiseux$arg -e 3 "$1" -d 2>&1
    echo
}

. common.sh
