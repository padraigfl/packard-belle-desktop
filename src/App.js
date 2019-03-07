import React, { Component, createContext } from "react";
import { Theme, ExplorerView, ExplorerIcon } from "packard-belle";
import cx from "classnames";
import logo from "./logo.svg";
import "./App.css";
import Explorer from "./components/ExplorerWindow";
import TaskBar from "./components/TaskBar";

const testOptions = [
  {
    title: "Test",
    icon: logo,
    onClick: () => {},
    options: [
      {
        title: "Test",
        icon: logo,
        onClick: () => {}
      }
    ]
  },
  {
    title: "Test2",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test3",
    icon: logo,
    onClick: () => {}
  },
  {
    title: "Test4",
    icon: logo,
    onClick: () => {}
  }
];

export const ProgramContext = createContext();

export const ScaleContext = createContext();

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

class ScaleProvider extends Component {
  state = {
    scale: 2,
    // changeScale: val =>
    //   typeof val === "number" ? this.setState(() => ({ scale: val })) : null
    changeScale: () => {
      this.setState(() => ({ scale: this.state.scale === 1 ? 2 : 1 }));
    }
  };
  render() {
    return (
      <ScaleContext.Provider value={this.state}>
        {this.props.children}
      </ScaleContext.Provider>
    );
  }
}

class Desktop extends Component {
  static contextType = ScaleContext;

  render() {
    return (
      <ProgramProvider>
        <ScaleContext.Consumer>
          {context => (
            <React.Fragment>
              <Theme
                className={cx("desktop", { desktopX2: context.scale === 2 })}
              >
                <ExplorerView options={testOptions}>
                  {testOptions.map(option => (
                    <ExplorerIcon key={option.title} {...option} />
                  ))}
                </ExplorerView>
                <TaskBar />
                <Explorer scale={this.context.scale} />
              </Theme>
              <button onClick={context.changeScale}>changeScale</button>
            </React.Fragment>
          )}
        </ScaleContext.Consumer>
      </ProgramProvider>
    );
  }
}

const App = () => (
  <ScaleProvider>
    <Desktop />
  </ScaleProvider>
);

// include corner thing if resizable
// body of explorer window needs to fill space

export default App;
