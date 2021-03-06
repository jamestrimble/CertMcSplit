CXX := g++
CXXFLAGS := -O3 -g -ggdb -march=native -std=c++17
all: mcsp

mcsp: mcsp.cpp graph.cpp graph.h proof_logging.cpp proof_logging.h
	$(CXX) $(CXXFLAGS) -Wall -o mcsp graph.cpp proof_logging.cpp mcsp.cpp -pthread
