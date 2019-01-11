#!/bin/sh

for i in *.dot; do 
	cat $i | sed "s/<[^>]*>//g"  | sed "s/\[label=/|/g" |sed "s/ -> /|/g" | grep ">" | sed "s/>\].*$//g" | sed -e "s/|/\t/g" | awk '{printf("%s -- %s -> %s\n", $1, $3, $2)}' > $i.txt;
done