#/bin/bash

sed -i '30s/^.*/ICFLAGS += $(BASE_ICFLAGS) $(ML_ICFLAGS) -DCLOSURE_SEQ -DFLOYDOPT -DDBMCACHE/' Makefile