#!/bin/bash
# $Id: show4.sh,v 1.1 2013-03-31 05:55:39 deraugla Exp $

arg=

function check
{
    echo "\$ ./puiseux$arg -e 3 '$1'"
    ../puiseux$arg -e 3 "$1" 2>&1
    echo
}

. common.sh
