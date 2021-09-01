#!/bin/sh

for i in ./*dot ; do

		cat $i | \
		# replace void element tags between IO separator
		sed "s/<[\/a-z]*>\/<[\/a-z]*>/ \/ /g" | \
		# remove void element tags
		sed "s/<[\/a-z]*>//g" | \
		# remove table element tag
		sed "s/<table[^>]*>//g" | \
		# replace =< by ="
		sed "s/=</=\"/g" | \
		# replace >] by "]
		sed "s/>\]/\"\]/g" \
		> $i.fixed ;
done
