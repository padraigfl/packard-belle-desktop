import React, { Component, createContext } from "react";
import nanoid from "nanoid";
import startMenuData from "../data/start";
import desktopData from "../data/desktop";

export const ProgramContext = createContext();

const sameProgram = a => b => a.id === b.id;
const notSameProgram = a => b => a.id !== b.id;

const addIdsToData = data =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return addIdsToData(d);
        }
        return {
          ...d,
          id: nanoid(),
          options: addIdsToData(d.options)
        };
      })
    : undefined;
const startWithIds = addIdsToData(startMenuData);
const desktopWithIds = addIdsToData(desktopData);

const initialize = (open, data) =>
  Array.isArray(data)
    ? data.map(d => {
        if (Array.isArray(d)) {
          return initialize(open, d);
        }
        return {
          ...d,
          onClick: !d.options
            ? (...params) => {
                open(d);
                if (d.onClick) {
                  d.onClick(...params);
                }
              }
            : undefined,
          options: initialize(open, d.options)
        };
      })
    : undefined;

class ProgramProvider extends Component {
  state = {
    startMenu: initialize(p => this.open(p), startWithIds),
    desktop: initialize(this.open, desktopWithIds),
    activePrograms: []
  };

  isProgramActive = program =>
    this.state.activePrograms.some(sameProgram(program));

  exit = program =>
    this.setState({
      activePrograms: this.state.activePrograms.filter(notSameProgram(program))
    });

  moveToTop = program => {
    const programIndex = this.state.activePrograms.findIndex(
      sameProgram(program)
    );
    if (programIndex === -1) {
      return;
    }
    this.setState({
      activePrograms: [
        ...this.state.activePrograms.filter(notSameProgram(program)),
        program
      ]
    });
  };

  open = program => {
    if (!program.component) {
      return;
    }
    if (this.isProgramActive(program)) {
      this.moveToTop(program);
      return;
    }
    this.setState({
      activePrograms: [...this.state.activePrograms, program]
    });
  };

  close = program => {
    if (!this.isProgramActive(program)) {
      return;
    }

    // this.windowClose(program);

    if (!program.background) {
      this.exit(program);
    }
  };

  render() {
    return (
      <ProgramContext.Provider
        value={{
          ...this.state,
          onClose: this.close,
          moveToTop: this.moveToTop
        }}
      >
        {this.props.children}
      </ProgramContext.Provider>
    );
  }
}

export default ProgramProvider;
