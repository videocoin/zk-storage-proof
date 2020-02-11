
FFLIBS := -lswscale -lavformat -lavcodec -lswresample -lavutil -lm
OTHERLIBS := -lcrypto -lstdc++

extract-frame: extract-frame.o sha256-util.o
	g++ -g -o extract-frame extract-frame.o sha256-util.o $(FFLIBS) $(OTHERLIBS)

clean: 
	rm extract-frame
