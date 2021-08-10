import re
import subprocess
import getopt
import time
import sys

def Profile():
    """ 
    --- doc ---
    Get the command line arguments and create the performance graph.
    --- usage ---
    Usage : $python3 mkGraph.py --path path/to/exe --arg1 first_arg --arg2 scnd_arg
    Options : 
     --arg3  third argument
     -t  create the runtime graph
     -p  create the productivity graph
     -m  compute the mean over several executions
     -c  maximum number of cores
     -s  step when incrementing over the number of cores
     -n  custom suffix for the name of the output graph
     -r  create the memory residency graph
    """

    path_exe = ""
    argu1 = ""
    argu2 = ""
    argu3 = ""
    ret_time = False
    ret_prod = False
    ret_residency = False
    mean_value = 1
    cores = ""
    core_step = ""
    name = ""

    argv = sys.argv[1:]

    try:
        opts, args = getopt.getopt(argv, "rtpc:s:n:m:", [
            'arg1=', 'arg2=', 'arg3=', 'path='])
        for opt, arg in opts:
            if opt == '--path':
                path_exe = arg
            elif opt == '--arg1':
                argu1 = arg
            elif opt == '--arg2':
                argu2 = arg
            elif opt == '--arg3':
                argu3 = arg
            elif opt == '-r':
                ret_residency = True
            elif opt == '-t':
                ret_time = True
            elif opt == '-p':
                ret_prod = True
            elif opt == '-m':
                mean_value = int(arg)
            elif opt == '-c':
                cores = arg
            elif opt == '-s':
                core_step = arg
            elif opt == '-n':
                name = arg
    except getopt.GetoptError:
        print(Profile.__doc__)
        exit(0)

    if len(path_exe)==0 or len(argu1)==0 or len(argu2)==0:
        print("Not enough arguments")
        exit(0)

    table_time = {}
    table_prod = {}
    table_residency = {}
    
    """
    if range_value:
        for maxTotient in range (int(argu2), int(argu1)+1, int(argu2)):
            t1=time.time()
            out = subprocess.check_output([path_exe, "1", str(maxTotient), "+RTS", "-s"],
                                          stderr=subprocess.STDOUT)
            t2 = time.time()
            tot_time = t2 - t1
            strOut = re.findall("Productivity\s+[0-9]+\.[0-9]+%",out.decode('ascii'))
            prod = re.findall("[0-9]+.[0-9]+",strOut[0])[0]
            table_time[str(maxTotient)] = ("%.2f" % tot_time)
            table_prod[str(maxTotient)] = prod
    """

        
    if len(core_step)>0 and len(cores)>0:
        for m in range (1,mean_value+1):           
            for nbCores in range (1,int(cores)+1,int(core_step)):
                ncores = "-N"+str(nbCores)
                t1=time.time()
                if len(argu3)>0:
                    out = subprocess.check_output([path_exe, argu1, argu2, argu3, "+RTS", ncores, "-s"],
                    stderr=subprocess.STDOUT)
                else:
                    out = subprocess.check_output([path_exe, argu1, argu2, "+RTS", ncores, "-s"],
                    stderr=subprocess.STDOUT)
                t2 = time.time()
                tot_time = t2 - t1
                strOut = re.findall("Productivity\s+[0-9]+\.[0-9]+%",out.decode('ascii'))
                prod = re.findall("[0-9]+.[0-9]+",strOut[0])[0]
                residency = re.findall("[0-9]+\s+MB\stotal",out.decode('ascii'))
                resi = re.findall("[0-9]+",residency[0])[0]
                if (nbCores in table_time):
                    table_time[nbCores] += float("%.2f" % tot_time)
                    table_prod[nbCores] += float(prod)
                    table_residency[nbCores] += float(resi)
                else:
                    table_time[nbCores] = float("%.2f" % tot_time)
                    table_prod[nbCores] = float(prod)
                    table_residency[nbCores] = float(resi)
                    
        for nbCores in range (1,int(cores)+1,int(core_step)):
            table_time[nbCores] /= mean_value
            table_prod[nbCores] /= mean_value
            table_residency[nbCores] /= mean_value

    else :
        t1=time.time()
        out = subprocess.check_output([path_exe, argu1, argu2, "+RTS", "-s"],
                    stderr=subprocess.STDOUT)
        t2 = time.time()
        tot_time = t2 - t1
        strOut = re.findall("Productivity\s+[0-9]+\.[0-9]+%",out.decode('ascii'))
        prod = re.findall("[0-9]+.[0-9]+%",strOut[0])[0]
        if (ret_time) : print ("Total time: " + ("%.2f" % tot_time))
        if (ret_prod) : print ("Productivity: " + prod)

    if ret_prod and len(table_prod)>0:
        plotG(table_prod,"prod"+str(name), "Productivity Graph", "Productivity(%)")

    if ret_time and len(table_time)>0:
        plotG(table_time,"runtime"+str(name), "Runtime Graph", "Time(s)")
        
    if ret_residency and len(table_residency)>0:
        plotG(table_residency,"memory"+str(name), "Memory Graph", "Memory(MB)")




def plotG(dictio, name, title, ylabel):
    f = open("perf"+str(name)+".txt", "w")
    for key, value in dictio.items():
        f.write(str(key) + " " + str(value) + "\n")
    f.close()

    f = open("gnuCmd.gnu", "w")
    f.write(
    'set terminal jpeg enhanced\n' + 
    'set output "'+ str(name) + '.jpeg"\n' +
    'set title "' + title + '"\n' +
    'set xlabel "Cores"\n' +
    'set ylabel "' + ylabel + '"\n' +
    'plot "perf' + str(name) +'.txt" using 1:2 with lines\n' +
    'unset output \n' +
    'quit')
    f.close()

    subprocess.call(["gnuplot", "./gnuCmd.gnu"])


Profile()
