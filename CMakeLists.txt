cmake_minimum_required(VERSION 3.10)
project(qrp2rup)
add_executable(qrp2rup clause_writer.cc cnf_circuit.cc grat_manager.cc io.cc proof_translator.cc qrp2rup.cc)
