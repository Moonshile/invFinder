#coding=utf-8

import time
import socket

HOST = '127.0.0.1'
PORT = 50008

s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
s.connect((HOST, PORT))
to_check = '11,1,n_flash_nodata,(!((Sta.UniMsg[3].Cmd = uni_get) & (Sta.UniMsg[3].Proc = 4) & (Sta.UniMsg[1].Cmd = uni_get) & (Sta.UniMsg[1].Proc = 2)))'
quit = '7,1,n_g2k'
s.sendall('%d,%s'%(len(to_check), to_check))
data = s.recv(1024)
print data
s.close()
