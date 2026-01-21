file(GLOB SOURCES *.cc)

add_executable(qrp2rup ${SOURCES})
set_target_properties(qrp2rup PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR})
