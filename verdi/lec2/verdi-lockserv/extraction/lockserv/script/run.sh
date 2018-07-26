#!/usr/bin/env bash
./LockServMain.native -debug -me $1 -port $2 -node Server,localhost:9000 -node Client-0,localhost:9001 -node Client-1,localhost:9002
