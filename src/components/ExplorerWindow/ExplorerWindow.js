import React, { Component } from "react";
import { WindowExplorer, ExplorerIcon, WindowAlert } from "packard-belle";
import * as icons from "../../icons";
import Window from "../tools/Window";
import buildMenu from "../../helpers/menuBuilder";
import "./_styles.scss";
import "../../icons/icons.scss";

const noop = () => {};

class Explorer extends Component {
  state = {
    loading: false,
  }
  handleClick = (entry) => {
    if (entry.failState) {
      this.toggleLoading();
      setTimeout(() => {
        this.setState({
          loading: false,
          title: entry.title,
          message: entry.failState.message,
          icon: entry.icon,
        })
      }, entry.failState.loadTime || 2000)
    }
  }

  toggleLoading = () => this.setState(state => ({ loading: !state.loading }));
  dismissMessage = () => this.setState({ message: null });

  render() {
    const { props } = this;
    return (
      <>
        <Window
          {...props}
          Component={WindowExplorer}
          className={this.state.loading && 'wait wait2'}
          explorerOptions={[
            {
              icon: icons.back,
              title: "Back",
              onClick: noop
            },
            {
              icon: icons.forward,
              title: "Forward",
              onClick: noop
            },
            {
              icon: icons.upDir,
              title: "Up",
              onClick: noop
            },
            {
              icon: icons.cut,
              title: "Cut",
              onClick: noop
            },
            {
              icon: icons.copy,
              title: "Copy",
              onClick: noop
            },
            {
              icon: icons.delete,
              title: "Delete",
              onClick: noop
            },
            {
              icon: icons.properties,
              title: "Properties",
              onClick: noop
            },
            {
              icon: icons.views,
              title: "Views"
            }
          ]}
          menuOptions={buildMenu(props)}
        >
          {props.data &&
            Array.isArray(props.data.content) &&
            props.data.content.map(entry => (
              <ExplorerIcon
                key={entry.title}
                title={entry.title}
                icon={icons[entry.icon]}
                className={entry.icon}
                onDoubleClick={!this.state.loading ? () => this.handleClick(entry) : undefined}
              />
            ))}
        </Window>
        {
          this.state.message && (
            <WindowAlert title={this.state.title} icon={icons.ieStop} onOK={this.dismissMessage} className="Window--active">
              {this.state.message}
            </WindowAlert>
          )
        }
      </>
    );
  }
}

export default Explorer;

// initialHeight, initialWidth, title, icon, footer, id,
// onClose, onMaximize, isActive, explorerOptions, chidlren, data, customSelect, Component
