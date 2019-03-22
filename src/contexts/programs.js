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
    activePrograms: [],
    openOrder: []
  };

  toggleTaskManager = () =>
    this.setState({ taskManager: !this.state.taskManager });

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
    if (this.isProgramActive(program) && !program.alwaysNew) {
      this.moveToTop(program);
      return;
    }
    this.setState({
      activePrograms: [...this.state.activePrograms, program],
      openOrder: [...this.state.openOrder, program.id]
    });
  };

  close = program => {
    if (!this.isProgramActive(program)) {
      return;
    }

    const taskBar = this.state.openOrder.filter(p => p.id !== program.id);
    this.setState({ openOrder: taskBar });
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
          onExit: this.exit,
          moveToTop: this.moveToTop,
          toggleTaskManager: this.toggleTaskManager
        }}
      >
        {this.props.children}
      </ProgramContext.Provider>
    );
  }
}

export default ProgramProvider;
