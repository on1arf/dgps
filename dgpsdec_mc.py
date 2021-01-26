import sys # for version check and argv

"""
DGPS decoder
input: 100  or 200 bps bits, encoded as bytes 0x00 or 0x01
output: text

Usage:
python3 navtexdec_mc.py [multicast-ip-address] [udp-port]


Version 0.1.0: 2020/Sep/19
Version 0.1.1: 2020/Dec/26
Version 0.2.0: 2021/Jan/26 bugfixes for ecef calculation and type-7 message, added message types 1, 5, 31, 35 and  36 

(C) Kristoff Bonne (ON1ARF), L. Van Heddegem (ON4CG)

This code is distributed under GPL license v. 3.0
https://www.gnu.org/licenses/gpl-3.0.en.html


Information source:
ITU Recommendation ITU-R M.823-1
https://www.itu.int/dms_pubrec/itu-r/rec/m/R-REC-M.823-3-200603-I!!PDF-E.pdf
https://web.archive.org/web/20150412020545/http://www.itu.int/dms_pubrec/itu-r/rec/m/R-REC-M.823-3-200603-I!!PDF-E.pdf


Note that this is not the 'final' document.
There are some differences between this document and the final recommendation as applied in real live transmissions.
One notable changes are the type 27 messages:
The station-name encoding is not done in 8 bit ascii, but
- 2 bits type of integrity test
- 5 bits that indicate what constellation the reference stations monitors
- the name of the station, encoded as 9 * 7 bits ascii


"""

# python version check
if sys.version_info.major < 3:
	raise RuntimeError("Python version 3 or newer required")
#end if

import socket
import struct

import threading


# disable warning in pylint (related to function __extractdata)
# pylint: disable=unbalanced-tuple-unpacking

# global data
defaultip="225.0.0.1"
defaultport=10000


DEBUG=True


# support functions

# scroll down to "dgpsdec_mc" for the main function


def __calcpar_i(word):
	par_contr = [0xBB1F3480,0x5D8F9A40,0xAEC7CD00,0x5763E680,0x6BB1F340,0x8B7A89C0]

	pc=0
	for exorpattern in par_contr:
		pc <<= 1
		pc += int('{:032b}'.format(int(word) & exorpattern).count('1'))%2
	#end for
	return pc
#end def


class __process_type9():
	def __init__(self,removeold=5000):
		self.all={}
		self.removeold=removeold
	#end __init

	def update(self,satid,s,udre,psc,rrc,iod,tcount,msgtype):
		key=(satid,iod)

		#DEBUG code
		d=self.all.get(key)
		if d is None:
			if DEBUG: print("T{t}DEBUG add".format(t=msgtype),tcount,key)
			ncount=1
		else:
			ncount=d[5]+1
		#end if

		self.all[key]=(s,udre,psc,rrc,tcount,ncount)
	#end def

	def printall(self, msgtype):
		def __fd(x):
			return format(x,'>6d')
		#end def

		def __ff(x):
			return format(x,'>-6.2f')

		for k in sorted(self.all.keys()):
			d=self.all[k]
			print("T"+str(msgtype),d[4],__fd(k[0]),__fd(k[1]),__fd(d[0]),__fd(d[1]),__ff(d[2]),__ff(d[3]),__fd(d[5]))
		#end for

		#only print the terminating lines if there is content
		if self.all.keys():
			print("T"+str(msgtype)+"-----------")
		#end if
	#end printall

	def cleanup(self,cnt,msgtype):
		o=cnt-self.removeold
		tmp=self.all.copy()
		changed=False
		for k in self.all.keys():
			d=self.all[k]
			if d[4] < o:
				if DEBUG: print("T{t}DEBUG del".format(t=msgtype),cnt,k,d[5])
				del tmp[k]
				changed=True
			#end if
		#end for

		if changed: self.all=tmp.copy()
#end class

def __extractdata(v,fieldlist):
	ret=[]

	for f in fieldlist[::-1]:
		if f > 0:	
			mask=(2**f)-1

			ret.append(v & mask)
			v>>=f
		else:
			ret.append(None)
		#end else - if
    #end for

	return ret[::-1]
#end def




def __getdataframes(s, w1,w2,maxnumframe):
	"""
	get data frames
	params:
		s: socket
		w1,w2: words as received
		maxnummsg: maximum number of frames
	returns:
		w1,w2: words as received
		data (list)
		l: length
	"""

	l=0 # length
	ret=[]

	# read up to "maxnumframe"
	for _ in range(maxnumframe):
		msgin=s.get(30) # read 1 frame of 30 bits

		# read bits into w1, invert order, copy 29th bit to w2
		for c in msgin:
			w2 = (w2 << 1) & 0xffffffff
			if w1 & 0x20000000 != 0: w2 |= 1 # copy 29th bit from w1 to 0th bit of w2
			w1 = ((w1 << 1) ^ (c&0x01)) & 0xffffffff
		#end for (char)

		# flip data-bits if last pre-bit (i.e. bit 30) is a '1'
		w1f = w1 ^ 0x3fffffc0 if w1 & 0x40000000 else w1

		# calculate parity
		par1=__calcpar_i(w1f)

		# message = bits 29 to 6 (exclude two 'prebits' and parity)
		# store only if frame is valid
		if par1 == (w1 & 0x0000003f):
			ret.append((w1f & 0x3fffffc0 ) >> 6)
			l+=1
		else:
			# break out if parity error
			break
		#end if

	#end for (msgword)

	return w1,w2,ret,l

#end getdataframes


def __formatashex6(l):
	return list(map(lambda x: format(x,'>06x'),l))

def __formatashex2(l):
	return list(map(lambda x: format(x,'>02x'),l))



# main function "DGPS decoder" starts here
def dgpsdec_mc(mcip=defaultip, mcport=defaultport):

	# get input bits from multicast stream
	class getinbits():
		def __init__ (self,sock):
			self.buff = []
			self.bufptr = 0
			self.bufsize = 0
			self.sock=sock
		#end def __init__

		def get(self,n):
			bits2get=n
			retbuf=[]

			while True:
				# get data from socket if buffer is empty
				if self.bufptr == self.bufsize:
					newbytes = self.sock.recv(10240)

					newbl=len(newbytes)
					if newbl == 0: continue # try again if no data read
					
					# store data in buffer and set pointer and size 
					self.buff=struct.unpack('B'*newbl,newbytes)
					self.bufptr=0
					self.bufsize=newbl
				#end if

				# get as much data from the buffer as possible
				nbits=min(bits2get,(self.bufsize-self.bufptr))

				retbuf += self.buff[self.bufptr:self.bufptr+nbits] # copy data from buffer

				self.bufptr += nbits # move buffer pointer upwards
				bits2get -= nbits

				if bits2get == 0: return retbuf # we have sufficient data, return

				# not yet enough data, get some more
				continue # return in loop to grab more data
			#end endless loop
		#end def get

	#end class getinbits():


	# ####################################
	######################################
	# main part of the function start here

	# receiving multicast in python, shameless stolen from
	# https://stackoverflow.com/questions/603852/how-do-you-udp-multicast-in-python

	# assert bind_group in groups + [None], \
	#     'bind group not in groups to join'
	sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)

	# allow reuse of socket (to allow another instance of python to run this
	# script binding to the same ip/port)
	sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

	sock.bind(('',mcport)) # bind to any ip-address

	#igmp join
	mreq=struct.pack('4sl',socket.inet_aton(mcip),socket.INADDR_ANY)
	sock.setsockopt(socket.IPPROTO_IP,socket.IP_ADD_MEMBERSHIP,mreq)


	indata=getinbits(sock)


	#type 9 processor
	t9=__process_type9()
	t31=__process_type9()

	#endless loop, break out with 'break' at the end of the file

	# init vars
	w1=0
	w2=0
	count=0

	lastt9cleanup=0
	lastt31cleanup=0


	while True:
		c=indata.get(1)
		if not c: break
		c=c[0]
		count+=1

		# create two 32-bit words
		w2 = (w2 << 1) & 0xffffffff
		if w1 & 0x20000000 != 0: w2 |= 1 # copy 29th bit from w1 to 0th bit of w2
		w1 = ((w1 << 1) ^ (c&0x01)) & 0xffffffff

		# flip data-bits if last pre-bit (i.e. bit 30) is a '1'
		w1f = w1 ^ 0x3fffffc0 if w1 & 0x40000000 else w1
		w2f = w2 ^ 0x3fffffc0 if w2 & 0x40000000 else w2

		# calculate parity
		par1=__calcpar_i(w1f)
		par2=__calcpar_i(w2f)

		# skip bit if parity does not match
		if (par1 != w1 & 0x0000003f) or (par2 != w2 & 0x0000003f):
			continue
		#end if


		# FEC-check is successfull!


		# make good-looking strings
		w1t=format(w1f & 0xffffffff,'>032b')
		w2t=format(w2f & 0xffffffff,'>032b')
		count_t=format(count,'>8d')

		# create data-records (remove the 2 trailing pre-bits, and the parity/fec data)
		w1r=(w1f & 0x3fffffc0) >> 6 
		w2r=(w2f & 0x3fffffc0) >> 6

		# do we have a sync-pattern?
		sync = True if w2r >> 16 == 0b01100110 else False

		if not sync:
			# not a sync-pattern, print out if debugging enabled
			if DEBUG: print(' ',count_t,w1t,w2t, flush=True)
			continue
		#end if

		# We have a sync-pattern, now extract data from the header
		msgtype,stationid=__extractdata(w2r,(6,10))
		mod_z, seq, msglen, stationhealth = __extractdata(w1r,(13,3,5,3))

		#scale modified_Z 
		mod_z *= 0.6

		print('S',count_t, end=' ')

		if DEBUG: print(w1t,w2t,end=' ')

		print(msgtype,stationid,round(mod_z,1),seq,msglen,stationhealth, flush=True)



		# type 3 message: ECEF location of the station
		if msgtype == 3:
			if msglen != 4: continue # message should be 4 frames

			# receive up to 4 frames
			w1,w2,type3msg,type3msglen=__getdataframes(indata,w1,w2,msglen)
			count+=type3msglen*30

			numtype3=int(type3msglen / 4) # how much messages did we receive correctly?
			print("type  3 message received:",msglen, __formatashex6(type3msg),numtype3)
			
			# did we get at a full message?
			if numtype3 == 1:
				m=type3msg[0]<<72|type3msg[1]<<48|type3msg[2]<<24|type3msg[3]
				ecefx,ecefy,ecefz=__extractdata(m,(32,32,32))

				if ecefx > 0x80000000: ecefx=-(0x100000000-ecefx)
				if ecefy > 0x80000000: ecefy=-(0x100000000-ecefy)
				if ecefz > 0x80000000: ecefz=-(0x100000000-ecefz)


				# scale ecefx, ecefy, ecefz
				ecefx /= 100
				ecefy /= 100
				ecefz /= 100

				print("T3",ecefx,ecefy,ecefz)
			#end if

			#done
			continue
		#end if (msgtype 3)

		# message type 6: null message
		if msgtype == 6:
			# null message
			# note: number of null frames can be 0 or 1
			if msglen not in (0,1): continue
			print("type  6 message received:", msglen)

			if msglen == 0: continue # length = 0 -> do nothing

			# just get next frame 
			w1,w2,_,_=__getdataframes(indata,w1,w2,msglen)
			count+=30

			# done
			continue
		#end if (msgtype 6)
 
		# message type 5: Constellation health message (GPS)
		if msgtype == 5:

			if msglen == 0:
				print("type 5 message received:", msglen)
				continue # length = 0 -> do nothing
			#end if

			# get all frames
			w1,w2,type5msg,type5msglen=__getdataframes(indata,w1,w2,msglen)
			count+=type5msglen*30

			print("type 5 message received:",msglen, __formatashex6(type5msg),type5msglen)

			if not type5msg:
				# no data received, so no data to output
				continue
			#end if

			for m in type5msg:
				reserved, satid, IssueOfDatalink, DataHealth, CN0, HealthEnable, NewNavData, LossOfSatWarn, TimeToUnhealthy, Unassigned=__extractdata(m,(1,5,1,3,5,1,1,1,4,2))

				# C/No: 00000 = untraced, else: 24 dB(Hz) + cno
				if CN0 > 0: CN0 += 24

				# time to unhealty: scale-factor = 5 minutes (300 seconds)
				TimeToUnhealthy *= 300

				print("T5",satid,IssueOfDatalink, DataHealth, CN0, HealthEnable, NewNavData, LossOfSatWarn, TimeToUnhealthy, reserved, Unassigned)
			#end for
			print()
			# done
			continue
		#end if (msgtype 5)

		# message type 36: special message (glonass)
		if msgtype == 36:

			if msglen == 0:
				print("type 36 message received:", msglen)
				continue # length = 0 -> do nothing

			# just get next frame 
			w1,w2,type36msg,type36msglen=__getdataframes(indata,w1,w2,msglen)
			count+=type36msglen*30

			print("type 36 message received:",msglen, __formatashex6(type36msg),type36msglen)
			if not type36msg:
				# no data received, so no data to output
				continue
			#end if

			s=[]
			for m in type36msg:
				strchars=__extractdata(m,(8,8,8))
				s+=strchars
			#end for

			# convert cyrillic from 8bit time (see page 14 - table 4 of Rec, ITU-R M.823-3) to unicode
			sc=[x if x < 128 else x + (0x410 - 0x80) for x in s]
			print("T36",''.join(map(chr,sc)))
			
			# done
			continue
		#end if (msgtype 36)

		# message type 7: station information (GPS)
		# message type 35: station information (glonass)
		#if msgtype == 7:
		if msgtype in (7,35):
			if msglen % 3 != 0: continue # length must be multiple of 3

			# read up to 'msglen' frames
			w1,w2,type7msg,type7msglen=__getdataframes(indata,w1,w2,msglen)
			count+=type7msglen*30

			numtype7=int(type7msglen/3) # how much messages did we receive correctly?
			if msgtype == 7:
				print("type  7 message received:",msglen, __formatashex6(type7msg),numtype7)
			else:
				print("type 35 message received:",msglen, __formatashex6(type7msg),numtype7)
			#end if

			cnt=0
			for _ in range(numtype7):
				t=type7msg[cnt:cnt+3]
				cnt+=3

				m=t[0]<<48|t[1]<<24|t[2] # concat 3 frames into 1 message
				lat,lon,brange,freq,health,statid,bitrate,modmode,synctype,bcoding=__extractdata(m,(16,16,10,12,3,9,3,1,1,1))

				# lat and lon are signed
				if lat > 0x8000: lat=-(0x10000-lat)
				if lon > 0x8000: lon=-(0x10000-lon)

				# scale lat, lon and freq
				lat = lat * 0.002747
				lon = lon * 0.005493
				freq = freq * 0.1 + 190

				# bitrate is table (negative values indicates an error)
				bitrate=(25,50,100,-3,150,200,-6,-7)[bitrate]

				print("T"+str(msgtype),round(lat,7),round(lon,7),brange,freq,health,statid,bitrate,modmode,synctype,bcoding)
			#end for

			# done
			continue
		# end if (msgtype 7)


		# message type 1: GPS correction data
		if msgtype == 1:
			# type 1 messages are length n*5 + (0, 2 or 4)
			expectedlen_t19 = (0,2,4)
			if msglen % 5 not in expectedlen_t19: continue #expect message length of n * 5 + 0, 2, 4

			# read up to "msglen" frames
			w1,w2,type1msg,type1msglen=__getdataframes(indata,w1,w2,msglen)


			type1msglenrem5=type1msglen%5
			type1msglendiv5=int(type1msglen/5)

			count+=type1msglen*30

			numtype1=type1msglendiv5*3+(0, 0, 1, 1, 2)[type1msglenrem5]  # how much messages did we receive correctly?

			print("type  1 message received:",msglen, __formatashex6(type1msg),numtype1)

			# parse every message
			for msgt1 in range(numtype1):
				d3=int(msgt1/3)
				offset=d3*5
				r3=msgt1%3
				
				if r3 == 0:
					m=type1msg[0+offset]<<24|type1msg[1+offset]
					fieldlist=(1,2,5,16,8,8,8)
				elif r3 == 1:
					m=type1msg[1+offset]<<48|type1msg[2+offset]<<24|type1msg[3+offset]
					fieldlist=(1,2,5,16,8,8,16)
				else:
					# r3 == 2:
					m=type1msg[3+offset]<<24|type1msg[4+offset]
					fieldlist=(1,2,5,16,8,8,0)
				#end else - elif - if

				s, udre, satid, psc, rrc, iod,_= __extractdata(m,fieldlist)

				# psc and rrc are signed
				if psc >=0x8000: psc = -(0x10000-psc)
				if rrc >=0x80: rrc = -(0x100-rrc)

				# scale and round psc and rrc, depending on value of scale-factor s
				psc = round(psc*0.02,2) if s == 0 else round(psc*0.32,2)
				rrc = round(rrc*0.002,3) if s == 0 else round(rrc*0.032,3)

				print("T1Sat ",satid,s,udre,psc,rrc,iod)
				t9.update(satid,s,udre,psc,rrc,iod,count,1)

			#end for

			# print out all information about all known satellites
			t9.printall(1)

			# do a cleanup of the satellite-list every 1000 words
			if count - lastt9cleanup > 1000:
				lastt9cleanup=count
				t9.cleanup(count,1)
			#end if

			# done
			continue
		#end if (msgtype 1)

		# message type 9: GPS correction data
		if msgtype == 9:
			expectedlen_t19 = (2,4,5)
			if msglen not in expectedlen_t19: continue #expect message length of 2, 4 or 5

			# read up to "msglen" frames
			w1,w2,type9msg,type9msglen=__getdataframes(indata,w1,w2,msglen)
			count+=type9msglen*30

			numtype9=(0,0,1,1,2,3)[type9msglen]  # how much messages did we receive correctly?

			print("type  9 message received:",msglen, __formatashex6(type9msg),numtype9)

			# parse every message
			for msgt9 in range(numtype9):
				if msgt9 == 0:
					m=type9msg[0]<<24|type9msg[1]
					fieldlist=(1,2,5,16,8,8,8)
				elif msgt9 == 1:
					m=type9msg[1]<<48|type9msg[2]<<24|type9msg[3]
					fieldlist=(1,2,5,16,8,8,16)
				else:
					#msgt9 == 2
					m=type9msg[3]<<24|type9msg[4]
					fieldlist=(1,2,5,16,8,8,0)
				#end else - elif - if

				s, udre, satid, psc, rrc, iod,_= __extractdata(m,fieldlist)

				# psc and rrc are signed
				if psc >=0x8000: psc = -(0x10000-psc)
				if rrc >=0x80: rrc = -(0x100-rrc)

				# scale and round psc and rrc, depending on value of scale-factor s
				psc = round(psc*0.02,2) if s == 0 else round(psc*0.32,2)
				rrc = round(rrc*0.002,3) if s == 0 else round(rrc*0.032,3)

				print("T9Sat ",satid,s,udre,psc,rrc,iod)
				t9.update(satid,s,udre,psc,rrc,iod,count,9)

			#end for

			# print out all information about all known satellites
			t9.printall(9)

			# do a cleanup of the satellite-list every 1000 words
			if count - lastt9cleanup > 1000:
				lastt9cleanup=count
				t9.cleanup(count,9)
			#end if

			# done
			continue
		#end if (msgtype 9)

		# message type 31: glonass correction data
		if msgtype == 31:
			# type 31 messages are length n*5 + (0, 2 or 4)
			expectedlen_t31 = (0,2,4)
			if msglen % 5 not in expectedlen_t31: continue #expect message length of n * 5 + 0, 2, 4

			# read up to "msglen" frames
			w1,w2,type31msg,type31msglen=__getdataframes(indata,w1,w2,msglen)


			type31msglenrem5=type31msglen%5
			type31msglendiv5=int(type31msglen/5)

			count+=type31msglen*30

			numtype31=type31msglendiv5*3+(0, 0, 1, 1, 2)[type31msglenrem5]  # how much messages did we receive correctly?

			print("type 31 message received:",msglen, __formatashex6(type31msg),numtype31)

			# parse every message
			for msgt31 in range(numtype31):
				d3=int(msgt31/3)
				offset=d3*5
				r3=msgt31%3
				
				if r3 == 0:
					m=type31msg[0+offset]<<24|type31msg[1+offset]
					fieldlist=(1,2,5,16,8,1,7,8)
				elif r3 == 1:
					m=type31msg[1+offset]<<48|type31msg[2+offset]<<24|type31msg[3+offset]
					fieldlist=(1,2,5,16,8,1,7,16)
				else:
					# r3 == 2:
					m=type31msg[3+offset]<<24|type31msg[4+offset]
					fieldlist=(1,2,5,16,8,1,7,0)
				#end else - elif - if

				s, udre, satid, psc, rrc,r, tb,_= __extractdata(m,fieldlist)

				# psc and rrc are signed
				if psc >=0x8000: psc = -(0x10000-psc)
				if rrc >=0x80: rrc = -(0x100-rrc)

				# scale and round psc and rrc, depending on value of scale-factor s
				psc = round(psc*0.02,2) if s == 0 else round(psc*0.32,2)
				rrc = round(rrc*0.002,3) if s == 0 else round(rrc*0.032,3)

				print("T31Sat ",satid,s,udre,psc,rrc,r,tb)
				t31.update(satid,s,udre,psc,rrc,tb,count,31)

			#end for
			# print out all information about all known satellites
			t31.printall(31)

			# do a cleanup of the satellite-list every 1000 words
			if count - lastt31cleanup > 1000:
				lastt31cleanup=count
				t31.cleanup(count,31)
			#end if

			# done
			continue
		#end if

		# message type 27: radio almanac (information about station and other stations in same region)
		if msgtype == 27:
			if msglen%6 != 0: continue # number of frames should a multiple of 6

			# extract up to 'msglen' frames
			w1,w2,type27msg,type27msglen=__getdataframes(indata,w1,w2,msglen)
			count+=type27msglen*30

			numtype27=int(type27msglen/6)  # how much messages did we receive correctly?
			print("type 27 message received:",msglen, __formatashex6(type27msg),numtype27)

			cnt=0
			# go over every message
			for _ in range(numtype27):
				t=type27msg[cnt:cnt+6]
				cnt+=6

				# concal all 6 frames into one 192 bit integer
				m=0
				for i in range(6):
					m<<=24
					m|=t[i]
				#end for

				#extract data + tempory storage for the station name
				lat,lon,refid1,freq,op,refid2,bitrate,dat,r,bc,integr,const,txt= __extractdata(m,(16,16,10,12,2,10,3,1,1,1,2,7,63))

				#extract station name
				c=__extractdata(txt,[7 for _ in range(9)]) # extract 9 times 1 character (7 bits) 
				name="".join(map(lambda x: '_' if x == 0 else chr(x),c))

				# lat and lon are signed
				if lat > 0x8000: lat=-(0x10000-lat)
				if lon > 0x8000: lon=-(0x10000-lon)

				# scale: lat, lon and freq
				lat = lat * 0.002747
				lon = lon * 0.005493
				freq = freq * 0.1 + 190

				# bitrate is a list  (negative values indicates an error
				bitrate=(25,50,100,200,-4,-5,-6,-7)[bitrate]

				print("T27",round(lat,7),round(lon,7),refid1,refid2,freq,op,bitrate,dat,r,bc,integr,const,name)
			#end for

			# done
			continue
		# end if (type 27)



		# catchall for unknown message types
		print("unknown type",msgtype)

		#done
		continue

	#end while (endless loop)

	print("done",flush=True)

# end 



# main function: get parameters and start dgpsdec_mc
def Main():
	try:
		mcip=sys.argv[1]
	except IndexError:
		mcip=defaultip
	#endtry

	try:
		mcport=sys.argv[2]
	except IndexError:
		mcport=defaultport
	#end try

	# start dgps decoder
	dgpsdec_mc(mcip,mcport)

	# we should never get (dgpsdec is an endless loop)
	print("Main done!",flush=True)

#end main

# kickstarter
if __name__ == "__main__": Main()
