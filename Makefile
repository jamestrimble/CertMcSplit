CXX := g++
CXXFLAGS := -O0 -march=native
all: mcsp

mcsp: mcsp.c graph.c graph.h
	$(CXX) $(CXXFLAGS) -Wall -std=c++11 -o mcsp graph.c mcsp.c -pthread
