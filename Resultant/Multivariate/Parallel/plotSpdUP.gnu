set terminal jpeg enhanced
set output "spdUp2.jpeg"
set title "Speed up / number of processors"
set xlabel "processors"
set ylabel "speed up"
plot "testsV1/Test2/lowPrimes/perfruntimelowPrimesSpdUp.txt" using 1:2 with lines title "Ver.1", "testsV1/Test3/lowPrimes/perfruntimelowPrimes2SpdUp.txt" using 1:2 with lines title "Ver.1.2", "testsV2/perfruntimeSpdUp.txt" using 1:2 with lines title "Ver.2.1" dt 2, "testsV3/lowPrimes/perfruntimelowPrimesSpdUp.txt" using 1:2 with lines title "Ver.2.2" dt 2, "testsV4/SpdUPV4.txt" using 1:2 with lines title "Ver.3" linecolor rgb "red" dt 5
unset output
quit