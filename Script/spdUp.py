import sys


def modFile(name,time):
    spdLines = ""
    
    f = open(name,'r')
    lines = f.readlines()
    for txt in lines:
        x = txt.split(" ")
        spdLines += x[0] + " " + str(time/float(x[1])) + "\n"
    f.close()
    
    spdUpFile = open(name.split(".")[0] + "SpdUp.txt", 'w')
    spdUpFile.writelines(spdLines)


modFile(sys.argv[1],float(sys.argv[2]))
