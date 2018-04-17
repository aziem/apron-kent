set style data histogram
set key left

set style fill pattern
set style histogram clustered

set ylabel "Time"
set xlabel "Experments (NumVar-NumConstraints)"

set xtics rotate out

plot "floydresults.csv" using 2:xtic(1) ti 'IncrClose Dbl Loop' lc rgbcolor "black", '' u 3 ti 'IncrClose Dbl Loop FloydOpt' lc rgbcolor "black"

set term png size 2000,1000
set output "floyd-graph.png"
replot