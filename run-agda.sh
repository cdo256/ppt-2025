#! /nix/store/4fvc5fm8bszmkydng1ivrvr5cbvr1g60-bash-5.2p37/bin/bash -e
#AGDA='/home/cdo/src/agda/dist-newstyle/build/x86_64-linux/ghc-9.4.8/Agda-2.8.0/build/agda/agda'
AGDA='/home/cdo/src/agda/result/bin/agda'
LIBRARY_FILE='./libraries'
#LIBRARY_FILE='/nix/store/4qh51my2mlkza8i136vj94ai5f4r6sll-libraries'
exec $AGDA --with-compiler=/nix/store/ycmnnrn2vfcrisca3wbmp899c88qvhx4-ghc-9.6.6-with-packages/bin/ghc --library-file=$LIBRARY_FILE "$@" 
