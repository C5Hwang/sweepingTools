add_library(btor2parser
        btor2parser/btor2parser.c
)
target_include_directories(btor2parser PRIVATE .)
set_target_properties(btor2parser PROPERTIES PUBLIC_HEADER btor2parser/btor2parser.h)
install(
        TARGETS btor2parser
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        PUBLIC_HEADER DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
)

file(GLOB BTORSIM
        btorsim/btorsimam.cpp
        btorsim/btorsimstate.cpp
        btorsim/btorsimvcd.cpp
        btorsim/btorsimhelpers.cpp
        btorsim/btorsimbv.c
        btorsim/btorsimrng.c
)

# *------------------------------------------------------------------------* #

add_executable(btorexpand
        simubtor/btorexpand.cpp
        btorfunc.h
        ${BTORSIM}
)
target_include_directories(btorexpand PRIVATE .)
target_link_libraries(btorexpand btor2parser)
install(TARGETS btorexpand DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(btoreliminate
        simubtor/btoreliminate.cpp
        btorfunc.h
        ${BTORSIM}
)
target_include_directories(btoreliminate PRIVATE .)
target_link_libraries(btoreliminate btor2parser)
install(TARGETS btoreliminate DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(btorextract
        simubtor/btorextract.cpp
        btorfunc.h
        ${BTORSIM}
)
target_include_directories(btorextract PRIVATE .)
target_link_libraries(btorextract btor2parser)
install(TARGETS btorextract DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(simubtor
        simubtor/simubtor.cpp
        btorfunc.h
        ${BTORSIM}
)
target_include_directories(simubtor PRIVATE .)
target_link_libraries(simubtor btor2parser)
install(TARGETS simubtor DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(btormerge
        simubtor/btormerge.cpp
        btorfunc.h
        ${BTORSIM}
)
target_include_directories(btormerge PRIVATE .)
target_link_libraries(btormerge btor2parser)
install(TARGETS btormerge DESTINATION ${CMAKE_INSTALL_BINDIR})

# *------------------------------------------------------------------------* #

add_executable(simuaiger
        simuaiger/simuaiger.cpp
        simuaiger/twosat.h
        btorfunc.h
        ${BTORSIM}
        ${CMAKE_SOURCE_DIR}/deps/aiger/aiger.c
)
target_include_directories(simuaiger PRIVATE . ${CMAKE_SOURCE_DIR}/deps/aiger)
target_link_libraries(simuaiger btor2parser)
install(TARGETS simuaiger DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(aigextract
        simuaiger/aigextract.cpp
        btorfunc.h
        ${BTORSIM}
        ${CMAKE_SOURCE_DIR}/deps/aiger/aiger.c
)
target_include_directories(aigextract PRIVATE . ${CMAKE_SOURCE_DIR}/deps/aiger)
target_link_libraries(aigextract btor2parser)
install(TARGETS aigextract DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(aigmerge
        simuaiger/aigmerge.cpp
        btorfunc.h
        ${BTORSIM}
        ${CMAKE_SOURCE_DIR}/deps/aiger/aiger.c
)
target_include_directories(aigmerge PRIVATE . ${CMAKE_SOURCE_DIR}/deps/aiger)
target_link_libraries(aigmerge btor2parser)
install(TARGETS aigmerge DESTINATION ${CMAKE_INSTALL_BINDIR})

# *------------------------------------------------------------------------* #

add_executable(btor2aiger
        btor2aiger.cpp
        ${CMAKE_SOURCE_DIR}/deps/aiger/aiger.c
)
target_include_directories(btor2aiger PRIVATE . ${CMAKE_SOURCE_DIR}/deps/aiger)
target_compile_options(btor2aiger PRIVATE -std=c++11 -Wall -g -g3 -ggdb)
target_link_libraries(btor2aiger btor2parser Boolector::boolector)
install(TARGETS btor2aiger DESTINATION ${CMAKE_INSTALL_BINDIR})

add_executable(aiger2cnf
        aiger2cnf.cpp
        btorfunc.h
        ${CMAKE_SOURCE_DIR}/deps/aiger/aiger.c
)
target_include_directories(aiger2cnf PRIVATE . ${CMAKE_SOURCE_DIR}/deps/aiger)
target_link_libraries(aiger2cnf btor2parser)
install(TARGETS aiger2cnf DESTINATION ${CMAKE_INSTALL_BINDIR})
