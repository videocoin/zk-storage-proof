
FFLIBS := -lswscale -lavformat -lavcodec -lswresample -lavutil -lm
OTHERLIBS := -lcrypto -lstdc++

gen-hash: gen-hash.o sha256-util.o
	g++ -g -o gen-hash gen-hash.o sha256-util.o $(FFLIBS) $(OTHERLIBS)

clean: 
	rm gen-hash
