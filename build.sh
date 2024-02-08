BUILT="./build/*"
for f in $BUILT; do rm -rf $f; done

A_FILES="./agda/*.agda"
for f in $A_FILES; do agda2hs $f -o build; done
