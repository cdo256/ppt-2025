#!/usr/bin/env -S bash -e
AGDA=`which agda`
LIBRARY_FILE='./libraries'
exec $AGDA --library-file=$LIBRARY_FILE --no-main "$@" 
