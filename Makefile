CXX := g++
CXXFLAGS := -O3 -g -ggdb -march=native -std=c++17
all: mcsp

mcsp: mcsp.cpp graph.cpp graph.h
	$(CXX) $(CXXFLAGS) -Wall -o mcsp graph.cpp mcsp.cpp -pthread
