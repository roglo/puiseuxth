#!/bin/bash
# $Id: show4.sh,v 1.2 2013-04-16 14:06:38 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg -e 3 '$1'"
    ../puiseux$arg -e 3 "$1" -d 2>&1
    echo
}

. common.sh
