#!/bin/sh
find . -type f -name '*.S' -exec grep -lx 'S2N_BN_SYMBOL([^)]*):' {} + |
    while read -r f; do
        sed -i -f /dev/stdin "$f" <<'EOF'
/^S2N_BN_SYMBOL([^)]*):$/ {
	:Loop
	n
	/^S2N_BN_SYMBOL([^)]*):$/ b Loop
	/^	_CET_ENDBR$/ b Out
	i\
	_CET_ENDBR
	:Out
}
EOF
done
