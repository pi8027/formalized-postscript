define(`EMBED',
    `syscmd(./coq2ps -m "MODULES" "$1" | tr -d "\n")dnl'
)dnl
define(`EMBEDPUSH',
    `{EMBED($1)}dnl'
)dnl
define(`SET_MODULES',
    `define(`MODULES', `$1')dnl'
)dnl
define(`ADD_MODULES',
    `define(`MODULES', MODULES `$1')dnl'
)dnl
SET_MODULES(`')dnl
