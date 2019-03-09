import React, { Component, createContext } from "react";

export const ProgramContext = createContext();

class ProgramProvider extends Component {
  state = {
    activePrograms: []
  };
  render() {
    return (
      <ProgramContext.Provider value={this.state}>
        {this.props.children}
      </ProgramContext.Provider>
    );
  }
}

export default ProgramProvider;
