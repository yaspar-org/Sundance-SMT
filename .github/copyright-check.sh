#!/usr/bin/env bash

check_file() {
  file=$1;
  head -n2 "$file" | grep -q -F 'Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.'
}

folder=${1?It is required to provide a folder}

error=0

while IFS= read -r -d '' f
do
  if ! check_file "$f"; then
    error=1
    echo "$f does not have a copyright banner!"
  fi
done <   <(find "$folder" -name '*.rs' -print0)

if [[ $error == 1 ]]; then
  echo "A copyright banner must be attached in the first two lines in every source code file!"
  exit 1
fi
exit 0