INC_DIR = -I../../ -I../common

INCLUDES := ../../tinyexr.h
OBJS := tinyexr.o cube2longlat.o

CXXFLAGS := -fsanitize=address -std=c++11 -O2
LDFLAGS := -fsanitize=address

TARGET=cube2longlat
 
all: $(TARGET)

$(TARGET): $(OBJS)
	$(CXX) -o $(TARGET) $(LDFLAGS) $(OBJS)

tinyexr.o: ../../tinyexr.cc
	$(CXX) $(CXXFLAGS) -c $(INC_DIR) $<

cube2longlat.o: cube2longlat.cc
	$(CXX) $(CXXFLAGS) -c $(INC_DIR) $<

.PHONY: clean
clean:
	rm -rf $(TARGET) $(OBJS)
