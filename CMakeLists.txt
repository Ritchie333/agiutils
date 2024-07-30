cmake_minimum_required(VERSION 3.26)
project(agic LANGUAGES C)

find_package(FLEX)
FLEX_TARGET(agic_flex agic/src/agic/agic.lex ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.c
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/lex.yy.h)

find_package(BISON)
BISON_TARGET(agic_parser agic/src/agic/agic.y ${CMAKE_CURRENT_BINARY_DIR}/y.tab.c
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/y.tab.h)

ADD_FLEX_BISON_DEPENDENCY(agic_flex agic_parser)

include_directories(${CMAKE_CURRENT_BINARY_DIR})
include_directories(agic/src/agic)

add_executable(agic
    agic/src/agic/agiavis.c
    agic/src/agic/agicore.c
    agic/src/agic/agierr.c
    agic/src/agic/agifunc.c
    agic/src/agic/agigoto.c
    agic/src/agic/agiobj.c
    agic/src/agic/agistr.c
    agic/src/agic/agitok.c
    agic/src/agic/boolean.c
    ${FLEX_agic_flex_OUTPUTS}
    ${BISON_agic_parser_OUTPUTS}
)

add_executable(agiglue
    agic/src/agiglue/agiglue.c)

add_executable(showlog
    showlog/showlog.c)

add_executable(volx
    volx2/volx.c)