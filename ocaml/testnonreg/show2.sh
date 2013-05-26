#!/bin/bash
# $Id: show2.sh,v 1.4 2013-05-26 20:00:19 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg \"$1\" -d"
    ../puiseux$arg "$1" -d 2>&1
    echo
}

. common.sh
