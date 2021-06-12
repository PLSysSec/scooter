CONCURRENCY=16
COUNT=10000
OUTDIR=$1
ADMIN=$2

do_bench () {
 ab -c $CONCURRENCY -n $COUNT ${@:3} http://localhost:8000/$2 > $OUTDIR/$1
}

mkdir -p $OUTDIR

do_bench "announcements" "announcements" ""
do_bench "account" "profile/account" -C "user_id=$ADMIN"
